#!/usr/bin/env python3
"""Extract generated certificates from a private generation JSONL."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--problems", type=Path, required=True)
    parser.add_argument("--family", required=True)
    parser.add_argument("--profile", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    problems = {row["id"]: row for row in read_jsonl(args.problems)}
    candidates = []
    for result in read_jsonl(args.results):
        if result.get("status") != "generated":
            continue
        problem = problems[result["problem_id"]]
        code = result["code"]
        payload = code.encode("utf-8")
        candidates.append(
            {
                "schema": "unrestricted-search-private-candidate-v1",
                "problem_id": result["problem_id"],
                "eq1_id": problem["eq1_id"],
                "eq2_id": problem["eq2_id"],
                "family": args.family,
                "profile": args.profile,
                "verdict": "false",
                "certificate_bytes": len(payload),
                "certificate_sha256": hashlib.sha256(payload).hexdigest(),
                "code": code,
            }
        )
    candidates.sort(key=lambda row: (row["eq1_id"], row["problem_id"]))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="\n") as stream:
        for row in candidates:
            stream.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")
    print(json.dumps({"candidates": len(candidates), "output": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
