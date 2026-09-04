#!/usr/bin/env python3
"""Independently reparse compressed ATP streams and audit stored statuses.

This verifier intentionally does not import ``remote_worker.py``.  It binds
every stream to its byte count and SHA-256 digest, then applies a second
implementation of the terminal-status policy.
"""

from __future__ import annotations

import argparse
import base64
import gzip
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Iterable
import zlib


SZS = re.compile(r"(?:^|\n)[#%]?\s*SZS status ([A-Za-z]+)")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|[()*=]")
SUCCESS = {"Theorem", "Unsatisfiable"}
COUNTER = {"Satisfiable", "CounterSatisfiable"}


def counter_policy(tool: str) -> tuple[str, bool, str]:
    if tool in {"vampire", "eprover"}:
        return "triv", False, "triv_proving_strategy_counter_is_nondecisive"
    if tool == "twee_complete":
        return "both", True, "parameter_free_twee_completion"
    raise ValueError(f"unknown tool: {tool}")


class EquationParser:
    def __init__(self, text: str):
        self.tokens = TOKEN.findall(text)
        if "".join(self.tokens) != re.sub(r"\s+", "", text):
            raise ValueError("unsupported equation syntax")
        self.position = 0

    def peek(self) -> str | None:
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def take(self, expected: str | None = None) -> str:
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise ValueError(f"expected {expected!r}, got {token!r}")
        self.position += 1
        return token

    def atom(self) -> tuple:
        if self.peek() == "(":
            self.take("(")
            value = self.term()
            self.take(")")
            return value
        token = self.take()
        if token in {"*", "=", "(" , ")"}:
            raise ValueError("expected variable")
        return ("var", token)

    def term(self) -> tuple:
        value = self.atom()
        while self.peek() == "*":
            self.take("*")
            value = ("mul", value, self.atom())
        return value

    def equation(self) -> tuple[tuple, tuple]:
        left = self.term()
        self.take("=")
        right = self.term()
        if self.peek() is not None:
            raise ValueError("trailing equation token")
        return left, right


def render_tptp(term: tuple, names: dict[str, str]) -> str:
    if term[0] == "var":
        variable = term[1]
        if variable not in names:
            names[variable] = f"X{len(names)}"
        return names[variable]
    return f"f({render_tptp(term[1], names)},{render_tptp(term[2], names)})"


def quantified(equation: str) -> str:
    left, right = EquationParser(equation).equation()
    names: dict[str, str] = {}
    body = f"{render_tptp(left, names)}={render_tptp(right, names)}"
    return f"! [{','.join(names.values())}] : ({body})" if names else f"({body})"


def problem_bytes(record: dict[str, Any]) -> bytes:
    return (
        f"fof(source,axiom,{quantified(record['equation1'])}).\n"
        f"fof(goal,conjecture,{quantified(record['equation2'])}).\n"
    ).encode("ascii")


def decode_stream(stream: dict[str, Any]) -> bytes:
    required = {"raw_bytes", "raw_sha256", "encoding", "compressed_bytes", "zlib_b64"}
    if set(stream) != required or stream["encoding"] != "zlib_base64_v1":
        raise ValueError("stream schema mismatch")
    packed = base64.b64decode(stream["zlib_b64"], validate=True)
    if len(packed) != stream["compressed_bytes"]:
        raise ValueError("compressed byte count mismatch")
    raw = zlib.decompress(packed)
    if len(raw) != stream["raw_bytes"]:
        raise ValueError("raw byte count mismatch")
    if hashlib.sha256(raw).hexdigest() != stream["raw_sha256"]:
        raise ValueError("raw SHA-256 mismatch")
    return raw


def reparse_attempt_details(tool: str, attempt: dict[str, Any]) -> dict[str, Any]:
    stdout = decode_stream(attempt["stdout"])
    stderr = decode_stream(attempt["stderr"])
    text = stdout.decode("utf-8", "replace")
    stderr_text = stderr.decode("utf-8", "replace")
    statuses = SZS.findall("\n" + text)
    success = [value for value in statuses if value in SUCCESS]
    counters = [value for value in statuses if value in COUNTER]
    direction, counter_trusted, trust_basis = counter_policy(tool)
    raw_conflict = bool(success and counters)
    conflict = bool(success and counters and counter_trusted)
    if tool == "vampire":
        proof = text.count("% SZS output start Proof") == 1 and text.count("% SZS output end Proof") == 1
    else:
        proof = text.count("SZS output start CNFRefutation") == 1 and text.count("SZS output end CNFRefutation") == 1
    clean = (
        attempt["returncode"] == 0
        and not attempt["timed_out"]
        and not attempt["memory_limited"]
    )
    if not attempt["cleanup_verified"]:
        status = "infrastructure_error"
    elif attempt["output_limited"]:
        status = "output_limit"
    elif conflict:
        status = "audit_error_conflicting_decisive_statuses"
    elif clean and success and proof:
        status = "theorem"
    elif clean and counters and counter_trusted:
        status = "counter_satisfiable"
    elif clean and counters:
        status = "completed_no_decisive_result"
    elif attempt["memory_limited"] or "out of memory" in stderr_text.lower():
        status = "memory_limit"
    elif (
        attempt["timed_out"]
        or any(value in {"Timeout", "ResourceOut"} for value in statuses)
        or (tool == "vampire" and ("% Time limit reached!" in text or "% Termination reason: Time limit" in text))
    ):
        status = "resource_exhausted"
    elif clean and success:
        status = "incomplete_theorem_output"
    elif tool == "eprover" and attempt["returncode"] == 8:
        status = "resource_exhausted"
    elif attempt["returncode"] in {0, 1}:
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
        "counter_satisfiable_trust_basis": trust_basis,
        "raw_status_conflict": raw_conflict,
        "decisive_status_conflict": conflict,
        "complete_tstp_proof_emitted": status == "theorem" and proof,
        "source_implication_proved": status == "theorem",
        "scientific_verdict": "TRIVIAL" if status == "theorem" else ("AUSTIN" if status == "counter_satisfiable" else ""),
    }


def reparse_attempt(tool: str, attempt: dict[str, Any]) -> str:
    return str(reparse_attempt_details(tool, attempt)["status"])


def aggregate_status(statuses: list[str]) -> str:
    if "audit_error_conflicting_decisive_statuses" in statuses or ("theorem" in statuses and "counter_satisfiable" in statuses):
        return "audit_error_conflicting_decisive_statuses"
    for status in (
        "theorem",
        "counter_satisfiable",
        "infrastructure_error",
        "output_limit",
        "memory_limit",
        "incomplete_theorem_output",
        "resource_exhausted",
        "completed_no_decisive_result",
    ):
        if status in statuses:
            return status
    return "completed_no_proof"


def iter_rows(path: Path) -> Iterable[dict[str, Any]]:
    opener = gzip.open if path.suffix == ".gz" else Path.open
    kwargs = {"mode": "rt", "encoding": "utf-8"} if path.suffix == ".gz" else {"mode": "r", "encoding": "utf-8"}
    with opener(path, **kwargs) as handle:
        for line_number, line in enumerate(handle, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(f"{path}:{line_number}: invalid JSON") from error
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: row is not an object")
            yield row


def audit_file(path: Path, input_path: Path | None = None) -> dict[str, Any]:
    inputs = None
    if input_path is not None:
        input_rows = list(iter_rows(input_path))
        inputs = {row["id"]: row for row in input_rows}
        if len(inputs) != len(input_rows):
            raise ValueError("duplicate frozen input ID")
    rows = 0
    tools: dict[str, int] = {}
    decisive = 0
    seen: set[str] = set()
    for row in iter_rows(path):
        rows += 1
        if row["record_id"] in seen:
            raise ValueError(f"duplicate result ID: {row['record_id']}")
        seen.add(row["record_id"])
        if inputs is not None:
            record = inputs.get(row["record_id"])
            if record is None:
                raise ValueError(f"unknown result ID: {row['record_id']}")
            if row["paper_dataset"] != record["paper_dataset"]:
                raise ValueError(f"{row['record_id']}: dataset binding mismatch")
            expected_problem_hash = hashlib.sha256(problem_bytes(record)).hexdigest()
            if row["problem_sha256"] != expected_problem_hash:
                raise ValueError(f"{row['record_id']}: problem SHA-256 mismatch")
        tool = row["tool"]
        tools[tool] = tools.get(tool, 0) + 1
        attempts = row["attempts"]
        reparsed = []
        for index, attempt in enumerate(attempts, 1):
            details = reparse_attempt_details(tool, attempt)
            status = str(details["status"])
            if status != attempt["status"]:
                raise ValueError(f"{row['record_id']}: attempt {index}: stored={attempt['status']} reparsed={status}")
            for field in (
                "szs_statuses",
                "decisive_szs_statuses",
                "classification_rule",
                "semantic_direction",
                "raw_counter_satisfiable_seen",
                "counter_satisfiable_trusted",
                "counter_satisfiable_trust_basis",
                "raw_status_conflict",
                "decisive_status_conflict",
                "complete_tstp_proof_emitted",
                "source_implication_proved",
                "scientific_verdict",
            ):
                if attempt.get(field) != details[field]:
                    raise ValueError(f"{row['record_id']}: attempt {index}: {field} mismatch")
            expected_allowance = 120.0
            if float(attempt["configured_solver_allowance_seconds"]) != expected_allowance:
                raise ValueError(f"{row['record_id']}: attempt {index}: allowance drift")
            if attempt["memory_metric"] != "sampled_aggregate_process_group_rss":
                raise ValueError(f"{row['record_id']}: attempt {index}: memory metric drift")
            if float(attempt["memory_sample_interval_seconds"]) != 0.05:
                raise ValueError(f"{row['record_id']}: attempt {index}: sampling drift")
            if int(attempt["memory_limit_bytes"]) != 2000 * 1024 * 1024:
                raise ValueError(f"{row['record_id']}: attempt {index}: memory limit drift")
            reparsed.append(status)
        expected = aggregate_status(reparsed)
        if expected != row["status"]:
            raise ValueError(f"{row['record_id']}: stored={row['status']} reparsed={expected}")
        expected_winner = next(
            (
                attempt
                for attempt in attempts
                if attempt["status"] in {"theorem", "counter_satisfiable"}
                or attempt.get("raw_counter_satisfiable_seen")
            ),
            None,
        )
        if row.get("winning_attempt_index") != (
            expected_winner["attempt_index"] if expected_winner else None
        ):
            raise ValueError(f"{row['record_id']}: winning attempt mismatch")
        expected_row_fields = {
            "source_implication_proved": expected == "theorem",
            "semantic_direction": attempts[0]["semantic_direction"],
            "raw_counter_satisfiable_seen": any(
                bool(attempt["raw_counter_satisfiable_seen"]) for attempt in attempts
            ),
            "counter_satisfiable_trusted": expected == "counter_satisfiable",
            "counter_satisfiable_trust_basis": attempts[0][
                "counter_satisfiable_trust_basis"
            ],
            "scientific_verdict": "TRIVIAL"
            if expected == "theorem"
            else ("AUSTIN" if expected == "counter_satisfiable" else ""),
            "complete_tstp_proof_emitted": expected == "theorem"
            and bool(expected_winner and expected_winner["complete_tstp_proof_emitted"]),
        }
        for field, value in expected_row_fields.items():
            if row.get(field) != value:
                raise ValueError(f"{row['record_id']}: row {field} mismatch")
        if row["resource_protocol"] != "uniform-process-tree-rss-v2":
            raise ValueError(f"{row['record_id']}: resource protocol drift")
        if row["status"] in {"theorem", "counter_satisfiable"}:
            decisive += 1
    if inputs is not None and seen != set(inputs):
        raise ValueError("result IDs do not exactly cover the frozen input")
    return {"rows": rows, "tools": tools, "decisive": decisive, "verified": True}


def packed(raw: bytes) -> dict[str, Any]:
    compressed = zlib.compress(raw, 9)
    return {
        "raw_bytes": len(raw),
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "encoding": "zlib_base64_v1",
        "compressed_bytes": len(compressed),
        "zlib_b64": base64.b64encode(compressed).decode("ascii"),
    }


def synthetic(stdout: bytes, *, rc: int = 0, timed_out: bool = False) -> dict[str, Any]:
    return {
        "returncode": rc,
        "timed_out": timed_out,
        "memory_limited": False,
        "output_limited": False,
        "cleanup_verified": True,
        "stdout": packed(stdout),
        "stderr": packed(b""),
    }


def self_test() -> dict[str, Any]:
    cases = [
        ("vampire", synthetic(b"% SZS status Timeout\n% SZS status CounterSatisfiable\n"), "completed_no_decisive_result"),
        ("vampire", synthetic(b"% SZS status Timeout\n% SZS status CounterSatisfiable\n", timed_out=True), "resource_exhausted"),
        ("vampire", synthetic(b"% SZS status Theorem\n"), "incomplete_theorem_output"),
        # The proof is decisive; the triv-direction counter status is raw-only.
        ("vampire", synthetic(b"% SZS status Theorem\n% SZS output start Proof\n% SZS output end Proof\n% SZS status CounterSatisfiable\n"), "theorem"),
        ("eprover", synthetic(b"# SZS status Theorem\n# SZS output start CNFRefutation\n# SZS output end CNFRefutation\n"), "theorem"),
        ("eprover", synthetic(b"# SZS status CounterSatisfiable\n"), "completed_no_decisive_result"),
        ("twee_complete", synthetic(b"% SZS status CounterSatisfiable\n"), "counter_satisfiable"),
    ]
    for tool, attempt, expected in cases:
        actual = reparse_attempt(tool, attempt)
        if actual != expected:
            raise AssertionError(f"synthetic classifier: expected {expected}, got {actual}")
    mutated = synthetic(b"% SZS status CounterSatisfiable\n")
    mutated["stdout"]["raw_sha256"] = "0" * 64
    try:
        reparse_attempt("vampire", mutated)
    except ValueError:
        pass
    else:
        raise AssertionError("stream hash mutation was not rejected")
    return {"synthetic_cases": len(cases), "hash_mutation_rejected": True, "verified": True}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path)
    parser.add_argument("--input", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if not args.self_test and args.results is None:
        parser.error("provide --self-test and/or --results")
    payload: dict[str, Any] = {}
    if args.self_test:
        payload["self_test"] = self_test()
    if args.results is not None:
        payload["results"] = audit_file(args.results, args.input)
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
