#!/usr/bin/env python3
"""Separate ALPS screened-corpus coverage from ALPS4141 pool duplication."""

from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path
from typing import Any

from audit_input_overlap import TermParser, render, variables


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--austin96", type=Path, required=True)
    parser.add_argument("--generality34", type=Path, required=True)
    parser.add_argument("--alps-final-status", type=Path, required=True)
    parser.add_argument("--alps-evaluation-pool", type=Path, required=True)
    parser.add_argument("--alps-commit", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    return parser.parse_args()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_law(text: str) -> str:
    text = text.replace("◇", "*").replace("⋄", "*").replace("⋆", "*")
    left, right = TermParser(text).equation()
    names = sorted(variables(left) | variables(right))
    canonical_names = [f"v{index}" for index in range(len(names))]
    candidates: list[str] = []
    for assigned in itertools.permutations(canonical_names):
        mapping = dict(zip(names, assigned))
        candidates.append(f"{render(left, mapping)}={render(right, mapping)}")
        candidates.append(f"{render(right, mapping)}={render(left, mapping)}")
    return min(candidates)


def etp_category(row: dict[str, Any]) -> str:
    if row["paper_dataset"] == "austin96":
        return "table20_2_austin96"
    if row.get("class") == "known_austin10":
        return "table20_1_known_austin10"
    if row.get("class") == "unknown_finite_status24":
        return "table20_3_unknown_finite_status24"
    raise ValueError(f"unrecognized ETP row category: {row['id']}")


def index_alps(rows: list[dict[str, Any]], label: str) -> dict[str, list[dict[str, Any]]]:
    result: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        key = canonical_law(str(row["law"]))
        result.setdefault(key, []).append(row)
    return result


def main() -> int:
    args = parse_args()
    etp_rows = read_jsonl(args.austin96) + read_jsonl(args.generality34)
    final_rows = read_jsonl(args.alps_final_status)
    pool_rows = read_jsonl(args.alps_evaluation_pool)
    final_by_law = index_alps(final_rows, "final_status")
    pool_by_law = index_alps(pool_rows, "evaluation_pool")

    matrix: list[dict[str, Any]] = []
    for row in etp_rows:
        key = canonical_law(str(row["source_equation"]))
        category = etp_category(row)
        eq_id = int(row.get("source_eq_id", row["eq1_id"]))
        final_match = final_by_law.get(key, [])
        pool_match = pool_by_law.get(key, [])
        matrix.append(
            {
                "category": category,
                "equation_id": f"E{eq_id}",
                "record_id": row["id"],
                "in_alps_final_status": bool(final_match),
                "in_alps_evaluation_pool": bool(pool_match),
                "alps_final_status": final_match[0].get("status", "") if final_match else "",
                "alps_pool_tier": pool_match[0].get("tier", "") if pool_match else "",
                "alps_pool_baseline_resolution": (
                    json.dumps(pool_match[0].get("baseline_resolution"), sort_keys=True)
                    if pool_match
                    else ""
                ),
            }
        )

    categories = (
        "table20_1_known_austin10",
        "table20_2_austin96",
        "table20_3_unknown_finite_status24",
    )
    per_category: dict[str, Any] = {}
    for category in categories:
        members = [row for row in matrix if row["category"] == category]
        per_category[category] = {
            "etp_total": len(members),
            "in_alps_final_status": sum(row["in_alps_final_status"] for row in members),
            "absent_from_alps_final_status": sum(
                not row["in_alps_final_status"] for row in members
            ),
            "in_alps_evaluation_pool": sum(
                row["in_alps_evaluation_pool"] for row in members
            ),
            "absent_from_alps_evaluation_pool": sum(
                not row["in_alps_evaluation_pool"] for row in members
            ),
            "final_status_values": dict(
                sorted(
                    Counter(
                        str(row["alps_final_status"])
                        for row in members
                        if row["in_alps_final_status"]
                    ).items()
                )
            ),
        }

    summary = {
        "schema": "alps-etp-coverage-v1",
        "matching": "equation trees modulo bijective variable renaming and equality symmetry",
        "sources": {
            "alps_commit": args.alps_commit,
            "austin96_sha256": file_sha256(args.austin96),
            "generality34_sha256": file_sha256(args.generality34),
            "alps_final_status_sha256": file_sha256(args.alps_final_status),
            "alps_evaluation_pool_sha256": file_sha256(args.alps_evaluation_pool),
        },
        "alps_layers": {
            "final_status": {
                "meaning": "screened corpus membership; this is the layer behind the 115/130 table",
                "records": len(final_rows),
            },
            "evaluation_pool": {
                "meaning": "the 4,141-record ATP/search evaluation pool used in the present experiment",
                "records": len(pool_rows),
            },
        },
        "categories": per_category,
        "totals": {
            "etp_total": len(matrix),
            "in_alps_final_status": sum(row["in_alps_final_status"] for row in matrix),
            "absent_from_alps_final_status": sum(
                not row["in_alps_final_status"] for row in matrix
            ),
            "in_alps_evaluation_pool": sum(
                row["in_alps_evaluation_pool"] for row in matrix
            ),
            "absent_from_alps_evaluation_pool": sum(
                not row["in_alps_evaluation_pool"] for row in matrix
            ),
        },
        "conclusion": "ALPS inclusion in the ETP table and duplication inside the 4,271-run matrix use different ALPS layers and must not be conflated.",
    }

    args.output_dir.mkdir(parents=True, exist_ok=False)
    with (args.output_dir / "summary.json").open(
        "w", encoding="utf-8", newline="\n"
    ) as handle:
        json.dump(summary, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")
    with (args.output_dir / "matrix.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        columns = list(matrix[0])
        writer = csv.DictWriter(handle, fieldnames=columns, lineterminator="\n")
        writer.writeheader()
        writer.writerows(matrix)
    print(json.dumps(summary, sort_keys=True, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
