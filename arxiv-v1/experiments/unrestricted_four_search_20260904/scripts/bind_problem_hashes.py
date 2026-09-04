#!/usr/bin/env python3
"""Bind released result and Judge rows to exact frozen problem statements."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def canonical_problem(row: dict) -> bytes:
    payload = {
        "id": row["id"],
        "eq1_id": row["eq1_id"],
        "eq2_id": row["eq2_id"],
        "equation1": row["equation1"],
        "equation2": row["equation2"],
    }
    return json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("ascii")


def write_jsonl(path: Path, rows: list[dict]) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n")


def main() -> int:
    inputs = read_jsonl(ROOT / "inputs" / "all_4187.jsonl")
    by_id = {row["id"]: row for row in inputs}
    if len(by_id) != 4187:
        raise ValueError("frozen input ID audit failed")
    problem_hashes = {
        problem_id: hashlib.sha256(canonical_problem(row)).hexdigest()
        for problem_id, row in by_id.items()
    }
    targets = (
        RESULTS / "per_profile_results.jsonl",
        RESULTS / "judge_receipts.jsonl",
        RESULTS / "trace_fluctuation_supplement.jsonl",
    )
    counts = {}
    for path in targets:
        rows = read_jsonl(path)
        for row in rows:
            problem = by_id[row["problem_id"]]
            if row["eq1_id"] != problem["eq1_id"] or row["eq2_id"] != problem["eq2_id"]:
                raise ValueError(f"equation ID mismatch: {row['problem_id']}")
            row["problem_sha256"] = problem_hashes[row["problem_id"]]
        write_jsonl(path, rows)
        counts[path.name] = len(rows)
    print(json.dumps({"bound": counts, "hash_definition": "sha256(canonical id,eq1_id,eq2_id,equation1,equation2)"}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
