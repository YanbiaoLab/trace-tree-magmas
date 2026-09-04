from __future__ import annotations

import argparse
import json
import sys
import threading
from collections import Counter
from itertools import islice
from pathlib import Path

from solver_runtime_sandbox.runner import (
    PooledSolverSandboxBatchRunner,
    SolverSandboxBatchRunner,
    iter_problems_jsonl,
)
from solver_runtime_sandbox.runtime import SolverSandboxRuntime
from solver_runtime_sandbox.settings import (
    configure_https_trust,
    load_environment,
    settings_from_env,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="run_solver_sandbox.py",
        description=(
            "Run one solver.py against a JSONL problem set with a fixed window of "
            "Alibaba Cloud Agent Sandboxes."
        ),
    )
    parser.add_argument("--solver", type=Path, required=True, help="Path to solver.py")
    parser.add_argument("--problems", type=Path, required=True, help="Input problem JSONL")
    parser.add_argument("--output", type=Path, required=True, help="Output result JSONL")
    parser.add_argument(
        "--concurrency",
        type=int,
        help="Active task window (default: SOLVER_SANDBOX_MAX_RUNNING)",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        help="Per-problem wall-clock limit (capped by configuration)",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Run only the first N non-empty problem records",
    )
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="Replace an existing output file",
    )
    parser.add_argument("--quiet", action="store_true", help="Suppress progress output")
    parser.add_argument(
        "--reuse-sandboxes",
        action="store_true",
        help="Upload once per Sandbox worker and run multiple problems sequentially",
    )
    parser.add_argument(
        "--hold-sandboxes-until-round-end",
        action="store_true",
        help="With --reuse-sandboxes, release every worker only after the full round ends",
    )
    parser.add_argument(
        "--sandbox-pool-file",
        type=Path,
        help=(
            "Persist Sandbox IDs and reconnect them across runner processes; "
            "requires --reuse-sandboxes"
        ),
    )
    parser.add_argument(
        "--generation-only",
        action="store_true",
        help="Capture a size-valid proof without contacting Judge v3",
    )
    parser.add_argument(
        "--judge-concurrency",
        type=int,
        help="Maximum simultaneous Judge v3 requests",
    )
    parser.add_argument(
        "--measure-memory",
        action="store_true",
        help="Sample solver process-tree RSS and Sandbox cgroup memory in real time",
    )
    parser.add_argument(
        "--memory-sample-interval",
        type=float,
        default=0.25,
        help="Peak-memory sampling interval in seconds (default: 0.25)",
    )
    parser.add_argument(
        "--memory-series-interval",
        type=float,
        default=1.0,
        help="Retained memory-series interval in seconds (default: 1.0)",
    )
    parser.add_argument(
        "--memory-first-window-seconds",
        type=float,
        default=300.0,
        help="First-window peak duration in seconds (default: 300)",
    )
    parser.add_argument(
        "--memory-limit-mib",
        type=int,
        help=(
            "Hard per-solver resident-memory ceiling in MiB, enforced across "
            "the complete process tree"
        ),
    )
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()

    load_environment()
    settings = settings_from_env()
    configure_https_trust(settings.sandbox_ca_cert)

    concurrency = settings.max_running if args.concurrency is None else args.concurrency
    if not 1 <= concurrency <= settings.max_running:
        parser.error(
            f"--concurrency must be between 1 and configured maximum {settings.max_running}"
        )
    if args.timeout_seconds is not None and args.timeout_seconds < 1:
        parser.error("--timeout-seconds must be at least 1")
    if args.limit is not None and args.limit < 1:
        parser.error("--limit must be at least 1")
    if args.memory_sample_interval <= 0 or args.memory_series_interval <= 0:
        parser.error("memory sampling intervals must be positive")
    if args.memory_first_window_seconds <= 0:
        parser.error("--memory-first-window-seconds must be positive")
    if args.judge_concurrency is not None and args.judge_concurrency <= 0:
        parser.error("--judge-concurrency must be positive")
    if args.memory_limit_mib is not None and args.memory_limit_mib <= 0:
        parser.error("--memory-limit-mib must be positive")
    if args.hold_sandboxes_until_round_end and not args.reuse_sandboxes:
        parser.error("--hold-sandboxes-until-round-end requires --reuse-sandboxes")
    if args.sandbox_pool_file is not None and not args.reuse_sandboxes:
        parser.error("--sandbox-pool-file requires --reuse-sandboxes")
    if not settings.e2b_api_key:
        parser.error("E2B_API_KEY is required in .env or the process environment")
    if not settings.judge_v3_base_url and not args.generation_only:
        parser.error("JUDGE_V3_BASE_URL is required in .env or the process environment")
    if not args.solver.is_file():
        parser.error(f"solver.py not found: {args.solver}")
    if args.solver.name != "solver.py":
        parser.error("--solver file must be named solver.py")
    if not args.problems.is_file():
        parser.error(f"problem JSONL not found: {args.problems}")
    if args.output.exists() and not args.overwrite:
        parser.error(f"output already exists: {args.output}; pass --overwrite to replace it")
    if args.output.resolve() in {args.solver.resolve(), args.problems.resolve()}:
        parser.error("--output must differ from --solver and --problems")

    try:
        solver_bytes = args.solver.read_bytes()
        SolverSandboxRuntime.validate_solver(solver_bytes)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    runtime = SolverSandboxRuntime(
        settings,
        generation_only=args.generation_only,
        judge_concurrency=args.judge_concurrency,
        measure_memory=args.measure_memory,
        memory_sample_interval=args.memory_sample_interval,
        memory_series_interval=args.memory_series_interval,
        memory_first_window_seconds=args.memory_first_window_seconds,
        memory_limit_bytes=(
            args.memory_limit_mib * 1024 * 1024
            if args.memory_limit_mib is not None
            else None
        ),
    )
    runner_class = (
        PooledSolverSandboxBatchRunner if args.reuse_sandboxes else SolverSandboxBatchRunner
    )
    runner_options = {
        "solver_bytes": solver_bytes,
        "concurrency": concurrency,
        "timeout_seconds": args.timeout_seconds,
    }
    if args.reuse_sandboxes:
        runner_options["hold_sandboxes_until_round_end"] = args.hold_sandboxes_until_round_end
    if args.sandbox_pool_file is not None:
        pool_path = args.sandbox_pool_file
        try:
            if pool_path.exists():
                pool_payload = json.loads(pool_path.read_text(encoding="utf-8"))
                sandbox_ids = pool_payload.get("sandbox_ids", [])
                if (not isinstance(sandbox_ids, list) or
                        not all(isinstance(item, str) and item for item in sandbox_ids)):
                    raise ValueError("sandbox_ids must be a list of non-empty strings")
                sandbox_ids = list(dict.fromkeys(sandbox_ids))
            else:
                sandbox_ids = []
        except (OSError, json.JSONDecodeError, ValueError) as exc:
            parser.error(f"invalid Sandbox pool file {pool_path}: {exc}")
        pool_lock = threading.Lock()

        def persist_pool(current_ids: list[str]) -> None:
            payload = {
                "schema": "stage2-sandbox-pool-v1",
                "sandbox_ids": sorted(set(current_ids)),
            }
            with pool_lock:
                pool_path.parent.mkdir(parents=True, exist_ok=True)
                temporary = pool_path.with_name(pool_path.name + ".tmp")
                temporary.write_text(
                    json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8",
                    newline="\n",
                )
                temporary.replace(pool_path)

        runner_options.update({
            "sandbox_ids": sandbox_ids,
            "retain_sandboxes": True,
            "pool_changed": persist_pool,
        })
    runner = runner_class(runtime, **runner_options)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    output_mode = "w" if args.overwrite else "x"
    completed = 0
    solved = 0
    statuses: Counter[str] = Counter()

    try:
        with (
            args.problems.open("r", encoding="utf-8") as problem_file,
            args.output.open(output_mode, encoding="utf-8") as output_file,
        ):
            problems = iter_problems_jsonl(problem_file)
            if args.limit is not None:
                problems = islice(problems, args.limit)
            for record in runner.run(problems):
                output_file.write(json.dumps(record.as_dict(), ensure_ascii=False) + "\n")
                output_file.flush()
                completed += 1
                solved += int(record.result.solved)
                statuses[record.result.status] += 1
                if not args.quiet and completed % 10 == 0:
                    print(
                        f"completed={completed} solved={solved}",
                        file=sys.stderr,
                        flush=True,
                    )
    except (OSError, ValueError) as exc:
        parser.exit(2, f"error: {exc}\n")

    if not args.quiet:
        print(
            f"completed={completed} solved={solved} statuses={dict(statuses)} output={args.output}",
            file=sys.stderr,
        )
    if statuses["infrastructure_error"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
