#!/usr/bin/env python3
"""Reproduce the generation phase in remote Sandboxes.

Raw outputs contain provider identifiers and therefore must be written to a
caller-owned private directory outside this artifact.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ADAPTER = ROOT / "runner" / "run_isolated_search.py"
PROFILES = {
    "trace_depth_sweep_soundfix_v5": (
        "trace",
        "all_4187.jsonl",
    ),
    "guarded_contract_first_v1": (
        "guarded",
        "final_supplemental_guarded_2.jsonl",
    ),
    "completion_hybrid_soundfix_v5": (
        "completion",
        "final_supplemental_completion_61.jsonl",
    ),
    "completion_generalized_index0_full_v1": (
        "completion",
        "completion_E9001325.jsonl",
    ),
    "completion_indexed_all_v1": (
        "completion",
        "final_supplemental_completion_indexed3.jsonl",
    ),
    "cnf_nf16_reverse_ties_completed_first_sound_v3": (
        "cnf",
        "final_supplemental_cnf_nf16_17.jsonl",
    ),
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--private-run-root", type=Path, required=True)
    parser.add_argument("--runner-root", type=Path, default=ROOT / "runner" / "vendor")
    parser.add_argument("--concurrency", type=int, default=120)
    parser.add_argument("--profile", action="append", choices=tuple(PROFILES))
    args = parser.parse_args()
    if not 1 <= args.concurrency <= 150:
        parser.error("--concurrency must be between 1 and 150")

    private_root = args.private_run_root.expanduser().resolve()
    if private_root == ROOT or ROOT in private_root.parents:
        parser.error("private outputs must be outside the public artifact")
    private_root.mkdir(parents=True, exist_ok=False)
    temp_root = private_root / "task_temp"
    temp_root.mkdir()
    selected = args.profile or list(PROFILES)

    environment = dict(os.environ)
    environment["TEMP"] = str(temp_root)
    environment["TMP"] = str(temp_root)
    environment["SOLVER_SANDBOX_RUNNER_ROOT"] = str(args.runner_root.resolve())

    records = []
    for profile in selected:
        family, input_name = PROFILES[profile]
        output = private_root / f"{profile}.generated.jsonl"
        solver = ROOT / "algorithms" / family / profile / "solver.py"
        problems = ROOT / "inputs" / input_name
        command = [
            sys.executable,
            str(ADAPTER),
            "--solver",
            str(solver),
            "--problems",
            str(problems),
            "--output",
            str(output),
            "--concurrency",
            str(args.concurrency),
            "--timeout-seconds",
            "125",
            "--generation-only",
            "--measure-memory",
            "--memory-sample-interval",
            "0.05",
            "--memory-series-interval",
            "1.0",
            "--memory-first-window-seconds",
            "175",
            "--memory-limit-mib",
            "2000",
            "--reuse-sandboxes",
            "--quiet",
        ]
        completed = subprocess.run(
            command,
            cwd=args.runner_root,
            env=environment,
            check=False,
        )
        records.append(
            {
                "profile": profile,
                "input": input_name,
                "output": output.name,
                "return_code": completed.returncode,
            }
        )
        if completed.returncode:
            break

    (private_root / "campaign_terminal.json").write_text(
        json.dumps(records, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    return 0 if len(records) == len(selected) and not records[-1]["return_code"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
