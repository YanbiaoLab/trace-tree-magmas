#!/usr/bin/env python3
"""Submit private candidate JSONL to Judge v3 with resumable raw output."""

from __future__ import annotations

import argparse
import json
import threading
import time
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from solver_runtime_sandbox.judge import DEFAULT_PROOF_POLICY, JUDGE_PROBLEM_FIELDS
from solver_runtime_sandbox.models import Stage2Problem
from solver_runtime_sandbox.settings import load_environment, settings_from_env


ROOT = Path(__file__).resolve().parents[1]


def read_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidates", type=Path, required=True)
    parser.add_argument("--problems", type=Path, default=ROOT / "inputs" / "all_4187.jsonl")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--concurrency", type=int, default=35)
    parser.add_argument(
        "--request-timeout-seconds",
        type=float,
        help="Client wait per Judge request; omit to wait for a terminal response.",
    )
    args = parser.parse_args()
    if args.concurrency < 1:
        parser.error("--concurrency must be positive")
    if args.request_timeout_seconds is not None and args.request_timeout_seconds <= 0:
        parser.error("--request-timeout-seconds must be positive")

    load_environment()
    settings = settings_from_env()
    if not settings.judge_v3_base_url:
        parser.error("JUDGE_V3_BASE_URL is required")
    verify_url = settings.judge_v3_base_url.rstrip("/") + "/verify"

    problems = {row["id"]: row for row in read_jsonl(args.problems)}
    candidates = read_jsonl(args.candidates)
    done = {
        (row["problem_id"], row["certificate_sha256"])
        for row in read_jsonl(args.output)
        if row.get("status") not in {"request_error", "client_timeout"}
    }
    selected = [
        row
        for row in candidates
        if (row["problem_id"], row["certificate_sha256"]) not in done
    ]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    lock = threading.Lock()

    def submit(candidate: dict) -> dict:
        started = time.monotonic()
        problem = Stage2Problem.model_validate(problems[candidate["problem_id"]])
        problem_payload = problem.model_dump(
            include=JUDGE_PROBLEM_FIELDS, exclude_none=True
        )
        problem_payload.setdefault("proof_policy", DEFAULT_PROOF_POLICY)
        request = urllib.request.Request(
            verify_url,
            data=json.dumps(
                {
                    "problem": problem_payload,
                    "verdict": candidate["verdict"],
                    "code": candidate["code"],
                    "cache_mode": "read_write",
                },
                ensure_ascii=False,
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        try:
            with urllib.request.urlopen(
                request, timeout=args.request_timeout_seconds
            ) as response:
                judge_response = json.loads(response.read().decode("utf-8"))
            status = judge_response.get("status", "unknown")
            error = None
        except TimeoutError as exc:
            judge_response = None
            status = "client_timeout"
            error = f"{type(exc).__name__}: client wait limit reached"
        except Exception as exc:
            judge_response = None
            status = "request_error"
            error = f"{type(exc).__name__}: {exc}"
        return {
            "schema": "unrestricted-search-private-judge-result-v1",
            "problem_id": candidate["problem_id"],
            "eq1_id": candidate["eq1_id"],
            "eq2_id": candidate["eq2_id"],
            "family": candidate["family"],
            "profile": candidate["profile"],
            "certificate_bytes": candidate["certificate_bytes"],
            "certificate_sha256": candidate["certificate_sha256"],
            "verdict": candidate["verdict"],
            "status": status,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "response": judge_response,
            "error": error,
        }

    with ThreadPoolExecutor(max_workers=args.concurrency) as executor:
        futures = [executor.submit(submit, row) for row in selected]
        with args.output.open("a", encoding="utf-8", newline="\n") as stream:
            for index, future in enumerate(as_completed(futures), 1):
                result = future.result()
                with lock:
                    stream.write(
                        json.dumps(result, ensure_ascii=False, separators=(",", ":")) + "\n"
                    )
                    stream.flush()
                print(
                    f"completed={index}/{len(selected)} eq1={result['eq1_id']} "
                    f"status={result['status']} elapsed={result['elapsed_seconds']}",
                    flush=True,
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
