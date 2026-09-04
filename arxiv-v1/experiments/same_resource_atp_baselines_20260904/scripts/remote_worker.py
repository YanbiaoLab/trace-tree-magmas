#!/usr/bin/env python3
"""Execute one pinned ATP job inside a remote sandbox.

This file is uploaded together with one hash-pinned Linux executable.  It has
no network dependency and emits a strict result file with compressed raw
streams.  It is not intended to run solver workloads on the controller host.
"""

from __future__ import annotations

import argparse
import base64
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import tempfile
import time
from typing import Any
import zlib


TOOL_HASHES = {
    "vampire": "81532e088c4ee1238d7ea1d8e868a2dccf8d358ad4d2126d257b4dda7f2e6bd9",
    "eprover": "d30317bad0c72ea702306f16661e0d155b81e637e2a2d33b4a1b71545f4bfd5f",
    "twee_complete": "a97d5ed05f2fe13549f9551fe190ceb4794581ea1d6dfa06f5f1042efe098126",
}
HEX64 = re.compile(r"^[0-9a-f]{64}$")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
TOKEN = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*|[()*=])")
SZS_STATUS = re.compile(r"(?:^|\n)[#%]?\s*SZS status ([A-Za-z]+)")

def counter_policy(tool: str) -> tuple[str, bool, str]:
    """Return encoding direction, trust, and the reason for that trust level.

    Vampire/CASC and E/auto are theorem-proving runs over a conjecture (the
    ``triv`` direction in ALPS).  A saturation status from those incomplete
    proving strategies is not a countermodel result.  The parameter-free Twee
    completion run is bidirectional and is the only mode here allowed to emit
    a scientific Austin verdict.
    """
    if tool in {"vampire", "eprover"}:
        return "triv", False, "triv_proving_strategy_counter_is_nondecisive"
    if tool == "twee_complete":
        return "both", True, "parameter_free_twee_completion"
    raise ValueError(f"unknown tool: {tool}")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


class Term:
    def __init__(self, name: str | None = None, left: "Term | None" = None, right: "Term | None" = None):
        self.name, self.left, self.right = name, left, right


class Parser:
    def __init__(self, text: str):
        self.tokens: list[str] = []
        position = 0
        while position < len(text):
            match = TOKEN.match(text, position)
            if match is None:
                raise ValueError(f"invalid equation syntax at offset {position}")
            self.tokens.append(match.group(1))
            position = match.end()
        self.position = 0

    def peek(self) -> str | None:
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def pop(self, expected: str | None = None) -> str:
        value = self.peek()
        if value is None or (expected is not None and value != expected):
            raise ValueError(f"expected {expected!r}, got {value!r}")
        self.position += 1
        return value

    def atom(self) -> Term:
        if self.peek() == "(":
            self.pop("(")
            value = self.term()
            self.pop(")")
            return value
        value = self.pop()
        if not IDENT.fullmatch(value):
            raise ValueError("invalid variable")
        return Term(name=value)

    def term(self) -> Term:
        value = self.atom()
        while self.peek() == "*":
            self.pop("*")
            value = Term(left=value, right=self.atom())
        return value

    def equation(self) -> tuple[Term, Term]:
        left = self.term()
        self.pop("=")
        right = self.term()
        if self.peek() is not None:
            raise ValueError("trailing token")
        return left, right


def variables(term: Term) -> set[str]:
    if term.name is not None:
        return {term.name}
    if term.left is None or term.right is None:
        raise ValueError("malformed term")
    return variables(term.left) | variables(term.right)


def tptp_term(term: Term, names: dict[str, str]) -> str:
    if term.name is not None:
        if term.name not in names:
            names[term.name] = f"X{len(names)}"
        return names[term.name]
    if term.left is None or term.right is None:
        raise ValueError("malformed term")
    return f"f({tptp_term(term.left, names)},{tptp_term(term.right, names)})"


def quantified_equation(left: Term, right: Term) -> str:
    names: dict[str, str] = {}
    equation = f"{tptp_term(left, names)}={tptp_term(right, names)}"
    if not names:
        return f"({equation})"
    return f"! [{','.join(names.values())}] : ({equation})"


def build_problem(equation1: str, equation2: str) -> str:
    source = Parser(equation1).equation()
    target = Parser(equation2).equation()
    return (
        f"fof(source,axiom,{quantified_equation(source[0], source[1])}).\n"
        f"fof(goal,conjecture,{quantified_equation(target[0], target[1])}).\n"
    )


def proc_group_rss_bytes(pgid: int) -> tuple[int, int]:
    total = 0
    count = 0
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / "stat").read_text(encoding="ascii")
            tail = stat[stat.rfind(")") + 2 :].split()
            if int(tail[2]) != pgid:  # field 5 pgrp after state/ppid/pgrp
                continue
            # A dead child can remain briefly as a zombie until its parent is
            # reaped.  It has no executable process or RSS and must not turn a
            # successful process-group cleanup into infrastructure_error.
            if tail[0] == "Z":
                continue
            status = (entry / "status").read_text(encoding="ascii", errors="replace")
            match = re.search(r"^VmRSS:\s+(\d+)\s+kB$", status, re.MULTILINE)
            if match:
                total += int(match.group(1)) * 1024
            count += 1
        except (FileNotFoundError, PermissionError, ValueError, OSError):
            continue
    return total, count


def kill_group(pgid: int) -> None:
    try:
        os.killpg(pgid, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 0.5
    while time.monotonic() < deadline:
        if proc_group_rss_bytes(pgid)[1] == 0:
            return
        time.sleep(0.02)
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def preexec(output_bytes: int) -> None:
    # Memory is deliberately not constrained with RLIMIT_AS.  All three ATPs
    # use the same sampled aggregate process-group RSS supervisor below.
    resource.setrlimit(resource.RLIMIT_FSIZE, (output_bytes, output_bytes))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def packed_stream(data: bytes) -> dict[str, Any]:
    compressed = zlib.compress(data, 9)
    return {
        "raw_bytes": len(data),
        "raw_sha256": sha256_bytes(data),
        "encoding": "zlib_base64_v1",
        "compressed_bytes": len(compressed),
        "zlib_b64": base64.b64encode(compressed).decode("ascii"),
    }


def classify(
    tool: str,
    stdout: bytes,
    stderr: bytes,
    returncode: int,
    timed_out: bool,
    memory_limited: bool,
    output_limited: bool,
    cleanup_verified: bool,
) -> dict[str, Any]:
    text = stdout.decode("utf-8", "replace")
    stderr_text = stderr.decode("utf-8", "replace")
    statuses = SZS_STATUS.findall("\n" + text)
    success = [value for value in statuses if value in {"Theorem", "Unsatisfiable"}]
    counters = [value for value in statuses if value in {"Satisfiable", "CounterSatisfiable"}]
    if tool == "vampire":
        complete_proof = text.count("% SZS output start Proof") == 1 and text.count("% SZS output end Proof") == 1
    else:
        complete_proof = text.count("SZS output start CNFRefutation") == 1 and text.count("SZS output end CNFRefutation") == 1
    direction, counter_trusted, counter_trust_basis = counter_policy(tool)
    raw_status_conflict = bool(success and counters)
    decisive_conflict = bool(success and counters and counter_trusted)
    clean_success_exit = returncode == 0 and not timed_out and not memory_limited
    if not cleanup_verified:
        status = "infrastructure_error"
    elif output_limited:
        status = "output_limit"
    elif decisive_conflict:
        status = "audit_error_conflicting_decisive_statuses"
    # A successful final decisive status takes priority over timeout text from
    # an earlier Vampire portfolio slice.  Wrapper timeout/memory kills never
    # receive this override because the process did not exit cleanly.
    elif clean_success_exit and success and complete_proof:
        status = "theorem"
    elif clean_success_exit and counters and counter_trusted:
        status = "counter_satisfiable"
    elif clean_success_exit and counters:
        # An observed SZS counter status is intentionally retained as raw
        # diagnostic evidence, but the scientific verdict is empty.
        status = "completed_no_decisive_result"
    elif memory_limited or "out of memory" in stderr_text.lower():
        status = "memory_limit"
    elif (
        timed_out
        or any(value in {"Timeout", "ResourceOut"} for value in statuses)
        or (
            tool == "vampire"
            and (
                "% Time limit reached!" in text
                or "% Termination reason: Time limit" in text
            )
        )
    ):
        status = "resource_exhausted"
    elif clean_success_exit and success:
        status = "incomplete_theorem_output"
    elif tool == "eprover" and returncode == 8:
        status = "resource_exhausted"
    elif returncode in {0, 1}:
        status = "completed_no_proof"
    else:
        status = "infrastructure_error"
    return {
        "status": status,
        "szs_statuses": statuses,
        "decisive_szs_statuses": success + counters,
        "classification_rule": "direction-and-completeness-aware-v3",
        "semantic_direction": direction,
        "raw_counter_satisfiable_seen": bool(counters),
        "counter_satisfiable_trusted": status == "counter_satisfiable",
        "counter_satisfiable_trust_basis": counter_trust_basis,
        "raw_status_conflict": raw_status_conflict,
        "decisive_status_conflict": decisive_conflict,
        "complete_tstp_proof_emitted": status == "theorem" and complete_proof,
        "source_implication_proved": status == "theorem",
        "scientific_verdict": "TRIVIAL" if status == "theorem" else ("AUSTIN" if status == "counter_satisfiable" else ""),
        "explicit_model_emitted": False,
        "explicit_infinite_carrier_emitted": False,
        "independent_certificate_accepted": False,
        "judge_v3_applicable": False,
        "judge_calls": 0,
        "stdout_utf8_valid": stdout.decode("utf-8", "replace").encode("utf-8") == stdout,
        "stderr_utf8_valid": stderr.decode("utf-8", "replace").encode("utf-8") == stderr,
    }


def run_attempt(tool: str, binary: Path, flags: list[str], problem: Path, hard_seconds: float, memory_bytes: int, output_bytes: int, attempt_index: int) -> dict[str, Any]:
    command = [str(binary), *flags, str(problem)]
    with tempfile.TemporaryDirectory(prefix="atp-attempt-") as temp:
        stdout_path = Path(temp) / "stdout"
        stderr_path = Path(temp) / "stderr"
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        cgroup_events_before = read_cgroup_memory_events()
        started = time.monotonic()
        with stdout_path.open("wb") as stdout_handle, stderr_path.open("wb") as stderr_handle:
            process = subprocess.Popen(
                command,
                stdin=subprocess.DEVNULL,
                stdout=stdout_handle,
                stderr=stderr_handle,
                start_new_session=True,
                preexec_fn=lambda: preexec(output_bytes),
            )
            timed_out = False
            memory_limited = False
            output_limited = False
            peak_rss = 0
            peak_processes = 0
            while process.poll() is None:
                elapsed = time.monotonic() - started
                rss, count = proc_group_rss_bytes(process.pid)
                peak_rss = max(peak_rss, rss)
                peak_processes = max(peak_processes, count)
                if rss >= memory_bytes:
                    memory_limited = True
                    kill_group(process.pid)
                    break
                try:
                    if stdout_path.stat().st_size >= output_bytes or stderr_path.stat().st_size >= output_bytes:
                        output_limited = True
                        kill_group(process.pid)
                        break
                except FileNotFoundError:
                    pass
                if elapsed >= hard_seconds:
                    timed_out = True
                    kill_group(process.pid)
                    break
                time.sleep(0.05)
            try:
                returncode = process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                kill_group(process.pid)
                returncode = process.wait(timeout=2)
            cgroup_events_after = read_cgroup_memory_events()
            oom_kill_delta = max(
                0,
                cgroup_events_after.get("oom_kill", 0)
                - cgroup_events_before.get("oom_kill", 0),
            )
            # A fast allocation burst can cross the sandbox cgroup limit
            # between 50 ms RSS samples.  The cgroup OOM counter is the
            # authoritative signal; the near-limit SIGKILL fallback covers
            # runtimes that do not expose memory.events.
            if oom_kill_delta > 0 or (
                returncode == -signal.SIGKILL
                and peak_rss >= int(memory_bytes * 0.95)
            ):
                memory_limited = True
            solver_finished = time.monotonic()
        kill_group(process.pid)
        cleanup_verified = proc_group_rss_bytes(process.pid)[1] == 0
        finished = time.monotonic()
        elapsed = finished - started
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        stdout = stdout_path.read_bytes()
        stderr = stderr_path.read_bytes()
    stable_command = [Path(command[0]).name, *command[1:-1], "problem.p"]
    return {
        "attempt_index": attempt_index,
        "command": stable_command,
        "configured_solver_allowance_seconds": hard_seconds,
        "solver_wall_seconds": round(solver_finished - started, 6),
        "cleanup_seconds": round(finished - solver_finished, 6),
        "elapsed_seconds": round(elapsed, 6),
        "child_cpu_seconds": round((after.ru_utime + after.ru_stime) - (before.ru_utime + before.ru_stime), 6),
        "returncode": returncode,
        "timed_out": timed_out,
        "memory_limited": memory_limited,
        "output_limited": output_limited,
        "cleanup_verified": cleanup_verified,
        "peak_process_group_rss_bytes": peak_rss,
        "peak_process_group_members": peak_processes,
        "memory_metric": "sampled_aggregate_process_group_rss",
        "memory_sample_interval_seconds": 0.05,
        "memory_limit_bytes": memory_bytes,
        "cgroup_oom_kill_delta": oom_kill_delta,
        **classify(tool, stdout, stderr, returncode, timed_out, memory_limited, output_limited, cleanup_verified),
        "stdout": packed_stream(stdout),
        "stderr": packed_stream(stderr),
    }


def read_cgroup_value(candidates: list[str]) -> str | None:
    for candidate in candidates:
        try:
            return Path(candidate).read_text(encoding="ascii").strip()
        except (FileNotFoundError, PermissionError, OSError):
            continue
    return None


def read_cgroup_memory_events() -> dict[str, int]:
    for candidate in (
        "/sys/fs/cgroup/memory.events",
        "/sys/fs/cgroup/memory/memory.oom_control",
    ):
        try:
            values: dict[str, int] = {}
            for line in Path(candidate).read_text(encoding="ascii").splitlines():
                parts = line.split()
                if len(parts) == 2 and parts[1].isdigit():
                    values[parts[0]] = int(parts[1])
            return values
        except (FileNotFoundError, PermissionError, OSError):
            continue
    return {}


def self_check(tool: str, binary: Path) -> dict[str, Any]:
    expected = TOOL_HASHES[tool]
    actual = sha256_file(binary)
    if actual != expected:
        raise ValueError("binary SHA-256 mismatch")
    process = subprocess.run([str(binary), "--version"], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15, check=False)
    return {
        "schema": "same-resource-atp-remote-self-check-v1",
        "tool": tool,
        "binary_sha256": actual,
        "version_returncode": process.returncode,
        "version_stdout": process.stdout.decode("utf-8", "replace")[:2000],
        "version_stderr": process.stderr.decode("utf-8", "replace")[:2000],
        "logical_cpu_count": os.cpu_count(),
        "cgroup_cpu_max": read_cgroup_value(["/sys/fs/cgroup/cpu.max"]),
        "cgroup_memory_max": read_cgroup_value(["/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"]),
        "network_required": False,
    }


def install_binary(tool: str, archive: Path, binary: Path) -> dict[str, Any]:
    compressed = archive.read_bytes()
    # The runtime image has a deliberately small writable filesystem.  Keep
    # only one on-disk copy: retain the archive in memory, unlink it, then
    # materialize the verified executable.
    archive.unlink()
    raw = gzip.decompress(compressed)
    expected = TOOL_HASHES[tool]
    if sha256_bytes(raw) != expected:
        raise ValueError("decompressed binary SHA-256 mismatch")
    binary.write_bytes(raw)
    binary.chmod(0o700)
    return {
        "schema": "same-resource-atp-binary-install-v1",
        "tool": tool,
        "archive_bytes": len(compressed),
        "binary_bytes": len(raw),
        "binary_sha256": expected,
    }


def run_job(job: dict[str, Any], binary: Path) -> dict[str, Any]:
    required = {"schema", "tool", "record", "wall_seconds", "memory_bytes", "output_bytes"}
    if set(job) != required or job.get("schema") != "same-resource-atp-job-v1":
        raise ValueError("job schema mismatch")
    tool = job["tool"]
    if tool not in TOOL_HASHES or sha256_file(binary) != TOOL_HASHES[tool]:
        raise ValueError("tool binding mismatch")
    record = job["record"]
    if not isinstance(record, dict) or set(record) != {"id", "paper_dataset", "equation1", "equation2"}:
        raise ValueError("record schema mismatch")
    if not all(isinstance(record[key], str) and record[key] for key in record):
        raise ValueError("invalid record")
    wall_seconds = float(job["wall_seconds"])
    memory_bytes = int(job["memory_bytes"])
    output_bytes = int(job["output_bytes"])
    if wall_seconds != 120.0 or memory_bytes != 2000 * 1024 * 1024 or output_bytes != 16 * 1024 * 1024:
        raise ValueError("resource envelope drift")
    with tempfile.TemporaryDirectory(prefix="same-resource-atp-") as temp:
        problem = Path(temp) / "problem.p"
        problem_text = build_problem(record["equation1"], record["equation2"])
        problem.write_text(problem_text, encoding="ascii", newline="\n")
        started = time.monotonic()
        attempts: list[dict[str, Any]] = []
        if tool == "vampire":
            flag_sets = [["--input_syntax", "tptp", "--mode", "portfolio", "--schedule", "casc", "-i", "500", "-t", "120", "-p", "tptp"]]
        elif tool == "eprover":
            flag_sets = [["--auto", "--proof-object", "--tstp-format", "--cpu-limit=120"]]
        elif tool == "twee_complete":
            # ALPS ``twee/complete`` default search, plus an output-only flag
            # so successful theorems carry a complete auditable proof block.
            flag_sets = [["--tstp", "--formal-proof"]]
        else:
            raise ValueError(f"unknown tool: {tool}")
        for index, flags in enumerate(flag_sets, 1):
            attempt = run_attempt(tool, binary, flags, problem, wall_seconds, memory_bytes, output_bytes, index)
            attempts.append(attempt)
            if (
                attempt["status"] in {"theorem", "counter_satisfiable", "infrastructure_error", "audit_error_conflicting_decisive_statuses"}
                or attempt.get("raw_counter_satisfiable_seen")
            ):
                break
        statuses = [attempt["status"] for attempt in attempts]
        if "audit_error_conflicting_decisive_statuses" in statuses or ("theorem" in statuses and "counter_satisfiable" in statuses):
            status = "audit_error_conflicting_decisive_statuses"
        elif "theorem" in statuses:
            status = "theorem"
        elif "counter_satisfiable" in statuses:
            status = "counter_satisfiable"
        elif "infrastructure_error" in statuses:
            status = "infrastructure_error"
        elif "output_limit" in statuses:
            status = "output_limit"
        elif "memory_limit" in statuses:
            status = "memory_limit"
        elif "incomplete_theorem_output" in statuses:
            status = "incomplete_theorem_output"
        elif "resource_exhausted" in statuses:
            status = "resource_exhausted"
        elif "completed_no_decisive_result" in statuses:
            status = "completed_no_decisive_result"
        else:
            status = "completed_no_proof"
        winner = next(
            (
                attempt
                for attempt in attempts
                if attempt["status"] in {"theorem", "counter_satisfiable"}
                or attempt.get("raw_counter_satisfiable_seen")
            ),
            None,
        )
        raw_counter_seen = any(bool(attempt.get("raw_counter_satisfiable_seen")) for attempt in attempts)
        direction, _counter_trusted, counter_trust_basis = counter_policy(tool)
        return {
            "schema": "same-resource-atp-result-v1",
            "tool": tool,
            "record_id": record["id"],
            "paper_dataset": record["paper_dataset"],
            "problem_sha256": sha256_bytes(problem_text.encode("ascii")),
            "status": status,
            "resource_protocol": "uniform-process-tree-rss-v2",
            "configured_solver_allowance_seconds": wall_seconds,
            "solver_wall_seconds": round(sum(attempt["solver_wall_seconds"] for attempt in attempts), 6),
            "cleanup_seconds": round(sum(attempt["cleanup_seconds"] for attempt in attempts), 6),
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "attempt_count": len(attempts),
            "winning_attempt_index": winner["attempt_index"] if winner else None,
            "source_implication_proved": status == "theorem",
            "semantic_direction": direction,
            "raw_counter_satisfiable_seen": raw_counter_seen,
            "counter_satisfiable_trusted": status == "counter_satisfiable",
            "counter_satisfiable_trust_basis": counter_trust_basis,
            "scientific_verdict": "TRIVIAL" if status == "theorem" else ("AUSTIN" if status == "counter_satisfiable" else ""),
            "explicit_model_emitted": False,
            "explicit_infinite_carrier_emitted": False,
            "complete_tstp_proof_emitted": status == "theorem" and bool(winner and winner["complete_tstp_proof_emitted"]),
            "independent_certificate_accepted": False,
            "judge_v3_applicable": False,
            "judge_calls": 0,
            "attempts": attempts,
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tool", choices=sorted(TOOL_HASHES), required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--job", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--self-check", action="store_true")
    parser.add_argument("--install-binary", action="store_true")
    parser.add_argument("--archive", type=Path)
    args = parser.parse_args()
    try:
        if args.install_binary:
            if args.archive is None:
                parser.error("--archive is required with --install-binary")
            payload = install_binary(args.tool, args.archive.resolve(strict=True), args.binary.resolve())
        elif args.self_check:
            payload = self_check(args.tool, args.binary.resolve(strict=True))
        else:
            if args.job is None or args.result is None:
                parser.error("--job and --result are required")
            payload = run_job(json.loads(args.job.read_text(encoding="utf-8")), args.binary.resolve(strict=True))
        text = json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n"
        if args.result is not None:
            args.result.write_text(text, encoding="utf-8", newline="\n")
        print(json.dumps({key: payload.get(key) for key in ("schema", "tool", "record_id", "status")}, sort_keys=True))
        return 0
    except Exception as error:
        print(json.dumps({"status": "worker_exception", "error_type": type(error).__name__, "error": str(error)[:2000]}, sort_keys=True), file=os.sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
