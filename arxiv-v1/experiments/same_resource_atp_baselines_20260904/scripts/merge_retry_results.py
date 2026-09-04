#!/usr/bin/env python3
"""Replace tainted primary ATP rows with exact-ID clean rerun rows."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


BAD = {
    "infrastructure_error",
    "unresolved_infrastructure_error",
    "audit_error_conflicting_decisive_statuses",
}


def read(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def index(rows: list[dict], field: str) -> dict[str, dict]:
    result = {str(row[field]): row for row in rows}
    if len(result) != len(rows):
        raise ValueError(f"duplicate {field}")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--primary", type=Path, required=True)
    parser.add_argument("--retry", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    input_ids = [row["id"] for row in read(args.input)]
    primary = index(read(args.primary), "record_id")
    retry = index(read(args.retry), "record_id")
    if set(primary) != set(input_ids):
        raise ValueError("primary results do not match the frozen input")
    expected_retry = {record_id for record_id, row in primary.items() if row["status"] in BAD}
    if set(retry) != expected_retry:
        raise ValueError("retry result IDs do not exactly match tainted primary rows")
    remaining_bad = sorted(record_id for record_id, row in retry.items() if row["status"] in BAD)
    if remaining_bad:
        raise ValueError(f"retry still contains tainted rows: {remaining_bad[:5]}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="\n") as handle:
        for record_id in input_ids:
            row = retry.get(record_id, primary[record_id])
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n")
    print(json.dumps({"rows": len(input_ids), "replaced": len(retry), "remaining_bad": 0}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
