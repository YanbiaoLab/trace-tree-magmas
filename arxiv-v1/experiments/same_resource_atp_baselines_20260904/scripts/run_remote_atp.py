#!/usr/bin/env python3
"""Orchestrate a resumable ATP campaign on reusable remote sandboxes.

The controller performs scheduling, hashing and persistence locally.  It never
executes an ATP binary on the controller host.  Sandbox identifiers and control
errors are written only to --private-lifecycle, which must be outside the
publishable experiment directory.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import gzip
import hashlib
import json
import os
from pathlib import Path
import queue
import random
import sys
import threading
import time
from typing import Any


TOOL_HASHES = {
    "vampire": "81532e088c4ee1238d7ea1d8e868a2dccf8d358ad4d2126d257b4dda7f2e6bd9",
    "eprover": "d30317bad0c72ea702306f16661e0d155b81e637e2a2d33b4a1b71545f4bfd5f",
    "twee_complete": "a97d5ed05f2fe13549f9551fe190ceb4794581ea1d6dfa06f5f1042efe098126",
}


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def append_fsync(path: Path, value: Any, lock: threading.Lock) -> None:
    payload = canonical(value) + "\n"
    with lock:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8", newline="\n") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def strict_rows(path: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    seen: set[str] = set()
    with path.open("r", encoding="utf-8") as handle:
        for ordinal, line in enumerate(handle, 1):
            if not line.strip():
                raise ValueError(f"blank input line {ordinal}")
            source = json.loads(line)
            record = {
                "id": source["id"],
                "paper_dataset": source["paper_dataset"],
                "equation1": source["equation1"],
                "equation2": source["equation2"],
            }
            if not all(isinstance(value, str) and value for value in record.values()):
                raise ValueError(f"invalid input line {ordinal}")
            if record["id"] in seen:
                raise ValueError(f"duplicate id {record['id']}")
            seen.add(record["id"])
            rows.append(record)
    return rows


def load_completed(path: Path, tool: str) -> set[str]:
    completed: set[str] = set()
    if not path.exists():
        return completed
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                raise ValueError(f"blank checkpoint line {line_number}")
            value = json.loads(line)
            if value.get("schema") != "same-resource-atp-result-v1" or value.get("tool") != tool:
                raise ValueError(f"checkpoint binding mismatch at line {line_number}")
            record_id = value.get("record_id")
            if not isinstance(record_id, str) or not record_id or record_id in completed:
                raise ValueError(f"invalid/duplicate checkpoint id at line {line_number}")
            completed.add(record_id)
    return completed


class Campaign:
    def __init__(self, args: argparse.Namespace, rows: list[dict[str, str]]):
        self.args = args
        self.rows = rows
        self.result_lock = threading.Lock()
        self.lifecycle_lock = threading.Lock()
        self.state_lock = threading.Lock()
        self.stop_event = threading.Event()
        self.task_queue: queue.Queue[tuple[dict[str, str], int]] = queue.Queue()
        self.owned: dict[str, Any] = {}
        self.released: set[str] = set()
        self.self_checks: list[dict[str, Any]] = []
        self.completed = 0
        self.status_counts: dict[str, int] = {}
        self.transient_errors = 0
        self.started = time.monotonic()

    def lifecycle(self, event: str, **fields: Any) -> None:
        # This ledger is intentionally private and may contain sandbox ids.
        append_fsync(
            self.args.private_lifecycle,
            {"schema": "same-resource-atp-private-lifecycle-v1", "event": event, "time": time.time(), **fields},
            self.lifecycle_lock,
        )

    def create_session(self, slot: int, generation: int = 0) -> Any:
        from e2b import Sandbox
        from solver_runtime_sandbox.runtime import _configure_e2b_envd_trust

        _configure_e2b_envd_trust(self.args.settings.sandbox_ca_cert)
        last_error: Exception | None = None
        for attempt in range(1, self.args.create_attempts + 1):
            try:
                sandbox = Sandbox.create(
                    template=self.args.settings.sandbox_template,
                    api_key=self.args.settings.e2b_api_key,
                    domain=self.args.settings.e2b_domain,
                    timeout=self.args.lease_seconds,
                    request_timeout=self.args.settings.request_timeout_seconds,
                    allow_internet_access=False,
                    validate_api_key=False,
                )
                sandbox_id = str(getattr(sandbox, "sandbox_id", ""))
                if not sandbox_id:
                    raise RuntimeError("created sandbox has no id")
                with self.state_lock:
                    self.owned[sandbox_id] = sandbox
                self.lifecycle("created", sandbox_id=sandbox_id, slot=slot, generation=generation, attempt=attempt)
                sandbox.set_timeout(self.args.lease_seconds, request_timeout=self.args.settings.request_timeout_seconds)
                sandbox.files.write(
                    "/tmp/same_resource_atp_worker.py",
                    self.args.worker_bytes,
                    user=self.args.settings.sandbox_user,
                    request_timeout=self.args.settings.request_timeout_seconds,
                )
                sandbox.files.write(
                    "/tmp/atp_tool.gz",
                    self.args.binary_transfer_bytes,
                    user=self.args.settings.sandbox_user,
                    request_timeout=self.args.settings.request_timeout_seconds,
                )
                chmod = sandbox.commands.run(
                    "chmod 700 /tmp/same_resource_atp_worker.py",
                    user=self.args.settings.sandbox_user,
                    timeout=30,
                    request_timeout=self.args.settings.request_timeout_seconds,
                )
                if chmod.exit_code != 0:
                    raise RuntimeError(f"remote chmod failed rc={chmod.exit_code}")
                installed = sandbox.commands.run(
                    f"python3 -B /tmp/same_resource_atp_worker.py --install-binary --tool {self.args.tool} --archive /tmp/atp_tool.gz --binary /tmp/atp_tool",
                    user=self.args.settings.sandbox_user,
                    timeout=60,
                    request_timeout=self.args.settings.request_timeout_seconds,
                )
                if installed.exit_code != 0:
                    raise RuntimeError(f"remote binary install failed rc={installed.exit_code}: {installed.stderr[-1000:]}")
                checked = sandbox.commands.run(
                    f"python3 -B /tmp/same_resource_atp_worker.py --self-check --tool {self.args.tool} --binary /tmp/atp_tool",
                    user=self.args.settings.sandbox_user,
                    timeout=30,
                    request_timeout=self.args.settings.request_timeout_seconds,
                )
                if checked.exit_code != 0:
                    raise RuntimeError(f"remote self-check failed rc={checked.exit_code}: {checked.stderr[-1000:]}")
                payload = json.loads(checked.stdout.strip().splitlines()[-1])
                # The command prints a compact envelope; run a result-file self-check for full data.
                selfcheck_path = f"/tmp/selfcheck_{slot}_{generation}.json"
                checked = sandbox.commands.run(
                    f"python3 -B /tmp/same_resource_atp_worker.py --self-check --tool {self.args.tool} --binary /tmp/atp_tool --result {selfcheck_path}",
                    user=self.args.settings.sandbox_user,
                    timeout=30,
                    request_timeout=self.args.settings.request_timeout_seconds,
                )
                if checked.exit_code != 0:
                    raise RuntimeError(f"remote full self-check failed rc={checked.exit_code}")
                full = json.loads(sandbox.files.read(selfcheck_path, format="text", user=self.args.settings.sandbox_user, request_timeout=self.args.settings.request_timeout_seconds))
                if full.get("binary_sha256") != TOOL_HASHES[self.args.tool]:
                    raise RuntimeError("remote binary binding mismatch")
                with self.state_lock:
                    self.self_checks.append(full)
                self.lifecycle("ready", sandbox_id=sandbox_id, slot=slot, generation=generation)
                return sandbox
            except Exception as error:  # noqa: BLE001
                last_error = error
                self.lifecycle("create_or_setup_error", slot=slot, generation=generation, attempt=attempt, error_type=type(error).__name__, error=str(error)[:2000])
                try:
                    if "sandbox" in locals():
                        self.release(sandbox, reason="setup_error")
                except Exception:
                    pass
                if attempt < self.args.create_attempts:
                    time.sleep(random.uniform(2 ** (attempt - 1), 1.5 * (2 ** (attempt - 1))))
        raise RuntimeError(f"could not create/setup slot {slot}: {last_error}")

    def release(self, sandbox: Any, reason: str) -> None:
        from solver_runtime_sandbox.runtime import _bounded_sandbox_kill

        sandbox_id = str(getattr(sandbox, "sandbox_id", ""))
        with self.state_lock:
            if sandbox_id in self.released:
                return
            self.released.add(sandbox_id)
        try:
            _bounded_sandbox_kill(sandbox, min(15.0, self.args.settings.request_timeout_seconds))
            self.lifecycle("released", sandbox_id=sandbox_id, reason=reason, success=True)
        except Exception as error:  # noqa: BLE001
            self.lifecycle("released", sandbox_id=sandbox_id, reason=reason, success=False, error_type=type(error).__name__, error=str(error)[:2000])

    def run_one(self, sandbox: Any, record: dict[str, str], infrastructure_attempt: int) -> dict[str, Any]:
        token = hashlib.sha256(f"{record['id']}|{infrastructure_attempt}".encode()).hexdigest()[:20]
        job_path = f"/tmp/job_{token}.json"
        result_path = f"/tmp/result_{token}.json"
        job = {
            "schema": "same-resource-atp-job-v1",
            "tool": self.args.tool,
            "record": record,
            "wall_seconds": 120,
            "memory_bytes": 2000 * 1024 * 1024,
            "output_bytes": 16 * 1024 * 1024,
        }
        sandbox.files.write(
            job_path,
            canonical(job).encode("utf-8"),
            user=self.args.settings.sandbox_user,
            request_timeout=self.args.settings.request_timeout_seconds,
        )
        command = sandbox.commands.run(
            f"python3 -B /tmp/same_resource_atp_worker.py --tool {self.args.tool} --binary /tmp/atp_tool --job {job_path} --result {result_path}",
            user=self.args.settings.sandbox_user,
            # The remote worker is the scientific 120 s authority.  The
            # command-stream wait includes envd transport and cleanup latency.
            timeout=180,
            request_timeout=self.args.settings.request_timeout_seconds,
        )
        if command.exit_code != 0:
            raise RuntimeError(f"worker command failed rc={command.exit_code}: {command.stderr[-1500:]}")
        result = json.loads(sandbox.files.read(result_path, format="text", user=self.args.settings.sandbox_user, request_timeout=self.args.settings.request_timeout_seconds))
        if result.get("schema") != "same-resource-atp-result-v1" or result.get("tool") != self.args.tool or result.get("record_id") != record["id"]:
            raise RuntimeError("remote result binding mismatch")
        return result

    def worker_loop(self, slot: int, sandbox: Any) -> None:
        generation = 0
        try:
            while not self.stop_event.is_set():
                try:
                    record, infrastructure_attempt = self.task_queue.get_nowait()
                except queue.Empty:
                    return
                try:
                    result = self.run_one(sandbox, record, infrastructure_attempt)
                except Exception as error:  # noqa: BLE001
                    with self.state_lock:
                        self.transient_errors += 1
                    self.lifecycle("task_error", sandbox_id=str(getattr(sandbox, "sandbox_id", "")), slot=slot, record_id=record["id"], infrastructure_attempt=infrastructure_attempt, error_type=type(error).__name__, error=str(error)[:2000])
                    self.release(sandbox, reason="task_error")
                    if infrastructure_attempt < self.args.infrastructure_retries:
                        self.task_queue.put((record, infrastructure_attempt + 1))
                    else:
                        terminal = {
                            "schema": "same-resource-atp-result-v1",
                            "tool": self.args.tool,
                            "record_id": record["id"],
                            "paper_dataset": record["paper_dataset"],
                            "problem_sha256": None,
                            "status": "unresolved_infrastructure_error",
                            "elapsed_seconds": None,
                            "attempt_count": 0,
                            "winning_attempt_index": None,
                            "source_implication_proved": False,
                            "explicit_model_emitted": False,
                            "explicit_infinite_carrier_emitted": False,
                            "complete_tstp_proof_emitted": False,
                            "independent_certificate_accepted": False,
                            "judge_v3_applicable": False,
                            "judge_calls": 0,
                            "attempts": [],
                        }
                        append_fsync(self.args.output, terminal, self.result_lock)
                        self.mark_completed(terminal["status"])
                    self.task_queue.task_done()
                    if self.task_queue.empty():
                        return
                    generation += 1
                    try:
                        sandbox = self.create_session(slot, generation)
                    except Exception as replacement_error:  # noqa: BLE001
                        self.lifecycle("replacement_failed", slot=slot, generation=generation, error_type=type(replacement_error).__name__, error=str(replacement_error)[:2000])
                        return
                    continue
                append_fsync(self.args.output, result, self.result_lock)
                self.mark_completed(result["status"])
                self.task_queue.task_done()
        finally:
            self.release(sandbox, reason="worker_finished")

    def mark_completed(self, status: str) -> None:
        with self.state_lock:
            self.completed += 1
            self.status_counts[status] = self.status_counts.get(status, 0) + 1

    def progress_loop(self, total: int) -> None:
        while not self.stop_event.wait(30):
            with self.state_lock:
                completed = self.completed
                counts = dict(sorted(self.status_counts.items()))
                transient = self.transient_errors
                active = len(self.owned) - len(self.released)
            elapsed = time.monotonic() - self.started
            print(canonical({"event": "progress", "completed_new": completed, "total_new": total, "elapsed_seconds": round(elapsed, 1), "active_sandboxes": active, "status_counts": counts, "transient_errors": transient}), flush=True)

    def execute(self) -> dict[str, Any]:
        for record in self.rows:
            self.task_queue.put((record, 1))
        total = len(self.rows)
        progress = threading.Thread(target=self.progress_loop, args=(total,), daemon=True)
        progress.start()
        sessions: list[tuple[int, Any]] = []
        try:
            with ThreadPoolExecutor(max_workers=min(self.args.creation_concurrency, self.args.concurrency)) as executor:
                futures = {executor.submit(self.create_session, slot): slot for slot in range(self.args.concurrency)}
                for future in as_completed(futures):
                    slot = futures[future]
                    try:
                        sessions.append((slot, future.result()))
                    except Exception as error:  # noqa: BLE001
                        self.lifecycle("initial_slot_failed", slot=slot, error_type=type(error).__name__, error=str(error)[:2000])
            if not sessions:
                raise RuntimeError("no sandbox session passed setup")
            print(canonical({"event": "pool_ready", "requested": self.args.concurrency, "ready": len(sessions)}), flush=True)
            with ThreadPoolExecutor(max_workers=len(sessions)) as executor:
                futures = [executor.submit(self.worker_loop, slot, sandbox) for slot, sandbox in sessions]
                for future in as_completed(futures):
                    future.result()
            if not self.task_queue.empty():
                raise RuntimeError(f"campaign ended with {self.task_queue.qsize()} queued rows")
        finally:
            self.stop_event.set()
            progress.join(timeout=2)
            with self.state_lock:
                remaining = [(sid, sb) for sid, sb in self.owned.items() if sid not in self.released]
            for _sid, sandbox in remaining:
                self.release(sandbox, reason="campaign_finally")
        with self.state_lock:
            summary = {
                "schema": "same-resource-atp-controller-summary-v1",
                "tool": self.args.tool,
                "new_terminal_records": self.completed,
                "status_counts": dict(sorted(self.status_counts.items())),
                "transient_infrastructure_errors": self.transient_errors,
                "requested_concurrency": self.args.concurrency,
                "ready_initial_sessions": len(sessions),
                "owned_unique_sandboxes": len(self.owned),
                "released_unique_sandboxes": len(self.released),
                "all_owned_released": set(self.owned) <= self.released,
                "elapsed_seconds": round(time.monotonic() - self.started, 3),
                "remote_self_check_count": len(self.self_checks),
                "remote_self_check_distinct": sorted({canonical(item) for item in self.self_checks}),
            }
        return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tool", choices=sorted(TOOL_HASHES), required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--worker", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--private-lifecycle", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--runtime-root", type=Path, required=True)
    parser.add_argument("--concurrency", type=int, required=True)
    parser.add_argument("--creation-concurrency", type=int, default=25)
    parser.add_argument("--create-attempts", type=int, default=3)
    parser.add_argument("--infrastructure-retries", type=int, default=3)
    parser.add_argument("--lease-seconds", type=int, default=10800)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--offset", type=int, default=0)
    parser.add_argument("--repeat-input", type=int, default=1)
    args = parser.parse_args()
    if not 1 <= args.concurrency <= 150:
        parser.error("--concurrency must be in 1..150")
    if not 1 <= args.creation_concurrency <= 25:
        parser.error("--creation-concurrency must be in 1..25")
    if not 1 <= args.create_attempts <= 5 or not 1 <= args.infrastructure_retries <= 5:
        parser.error("retry counts must be in 1..5")
    if args.repeat_input < 1:
        parser.error("--repeat-input must be positive")
    return args


def main() -> int:
    args = parse_args()
    runtime_root = args.runtime_root.resolve(strict=True)
    sys.path.insert(0, str(runtime_root))
    os.environ["SOLVER_SANDBOX_ENV_FILE"] = str(runtime_root / ".env")
    from solver_runtime_sandbox.settings import configure_https_trust, load_environment, settings_from_env

    load_environment()
    settings = settings_from_env()
    configure_https_trust(settings.sandbox_ca_cert)
    if not settings.e2b_api_key:
        raise RuntimeError("E2B_API_KEY is not configured")
    binary = args.binary.resolve(strict=True)
    worker = args.worker.resolve(strict=True)
    if file_sha256(binary) != TOOL_HASHES[args.tool]:
        raise ValueError("local binary hash mismatch")
    rows = strict_rows(args.input.resolve(strict=True))
    rows = rows[args.offset : None if args.limit is None else args.offset + args.limit]
    if args.repeat_input > 1:
        if len(rows) != 1:
            raise ValueError("--repeat-input requires exactly one selected input row")
        base = rows[0]
        rows = [{**base, "id": f"{base['id']}::rep{index:04d}"} for index in range(1, args.repeat_input + 1)]
    completed = load_completed(args.output, args.tool)
    rows = [row for row in rows if row["id"] not in completed]
    args.settings = settings
    args.binary_bytes = binary.read_bytes()
    args.binary_transfer_bytes = gzip.compress(args.binary_bytes, compresslevel=9, mtime=0)
    args.worker_bytes = worker.read_bytes()
    args.output = args.output.resolve()
    args.private_lifecycle = args.private_lifecycle.resolve()
    args.summary = args.summary.resolve()
    print(canonical({"event": "campaign_start", "tool": args.tool, "selected_missing_rows": len(rows), "already_completed": len(completed), "concurrency": args.concurrency, "binary_sha256": TOOL_HASHES[args.tool], "binary_bytes": len(args.binary_bytes), "transfer_bytes": len(args.binary_transfer_bytes)}), flush=True)
    if not rows:
        atomic_json(args.summary, {"schema": "same-resource-atp-controller-summary-v1", "tool": args.tool, "new_terminal_records": 0, "already_completed": len(completed), "all_owned_released": True})
        return 0
    campaign = Campaign(args, rows)
    summary = campaign.execute()
    summary["already_completed_before_run"] = len(completed)
    summary["selected_missing_before_run"] = len(rows)
    atomic_json(args.summary, summary)
    print(canonical({"event": "campaign_complete", **{key: summary[key] for key in ("tool", "new_terminal_records", "status_counts", "owned_unique_sandboxes", "all_owned_released", "elapsed_seconds")}}), flush=True)
    return 0 if summary["all_owned_released"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
