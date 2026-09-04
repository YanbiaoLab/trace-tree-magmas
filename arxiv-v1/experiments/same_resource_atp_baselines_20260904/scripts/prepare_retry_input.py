#!/usr/bin/env python3
"""Select infrastructure-tainted rows for a clean remote rerun."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


RETRY_STATUSES = {
    "infrastructure_error",
    "unresolved_infrastructure_error",
    "audit_error_conflicting_decisive_statuses",
}


def rows(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result_rows = rows(args.results)
    retry_ids = {row["record_id"] for row in result_rows if row["status"] in RETRY_STATUSES}
    input_rows = rows(args.input)
    selected = [row for row in input_rows if row["id"] in retry_ids]
    if len(selected) != len(retry_ids):
        raise ValueError("retry IDs do not bind one-to-one to the frozen input")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="\n") as handle:
        for row in selected:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n")
    print(json.dumps({"retry_rows": len(selected), "statuses": sorted(RETRY_STATUSES)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
