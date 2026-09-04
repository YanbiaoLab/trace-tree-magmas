#!/usr/bin/env python3
"""Independently recompute the compact public result summary."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FAMILIES = ("trace", "guarded", "completion", "cnf")


def read_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def source_members(row: dict, prefix: str) -> list[str]:
    members = [
        str(value)
        for value in row.get("equivalent_record_ids", [row["id"]])
        if str(value).startswith(prefix)
    ]
    if str(row["id"]).startswith(prefix) and str(row["id"]) not in members:
        members.append(str(row["id"]))
    return sorted(set(members))


def test_set_breakdown(input_rows: list[dict], families: dict[str, set[str]]) -> dict:
    input_by_id = {str(row["id"]): row for row in input_rows}
    if len(input_by_id) != len(input_rows):
        raise ValueError("duplicate deduplicated benchmark ID")
    union = set().union(*families.values())

    def view(name: str, prefixes: tuple[str, ...]) -> dict:
        representative_members: dict[str, list[str]] = {}
        for representative_id, row in input_by_id.items():
            members = sorted(
                {
                    member
                    for prefix in prefixes
                    for member in source_members(row, prefix)
                }
            )
            if members:
                representative_members[representative_id] = members
        original_records = {
            member for members in representative_members.values() for member in members
        }

        def coverage(problem_ids: set[str]) -> dict:
            hit_representatives = set(representative_members) & problem_ids
            covered_records = {
                member
                for representative_id in hit_representatives
                for member in representative_members[representative_id]
            }
            direct = {
                representative_id
                for representative_id in hit_representatives
                if any(representative_id.startswith(prefix) for prefix in prefixes)
            }
            return {
                "accepted_equivalence_classes": len(hit_representatives),
                "covered_original_records_via_equivalence": len(covered_records),
                "accepted_representatives_with_source_native_id": len(direct),
            }

        return {
            "name": name,
            "original_records": len(original_records),
            "alpha_symmetry_equivalence_classes": len(representative_members),
            "collapsed_redundant_records": len(original_records) - len(representative_members),
            "families": {
                family: coverage(families[family]) for family in FAMILIES
            },
            "four_family_union": coverage(union),
        }

    order5 = view("order5", ("austin96::", "generality34::"))
    alps = view("alps4141", ("alps4141::",))
    cross_source = sum(
        bool(source_members(row, "alps4141::"))
        and bool(source_members(row, "austin96::") or source_members(row, "generality34::"))
        for row in input_rows
    )
    if order5["original_records"] != 130 or order5["alpha_symmetry_equivalence_classes"] != 130:
        raise ValueError("order5 source-view denominator drift")
    if alps["original_records"] != 4141 or alps["alpha_symmetry_equivalence_classes"] != 4140:
        raise ValueError("ALPS4141 source-view denominator drift")
    if cross_source != 83:
        raise ValueError("cross-source overlap drift")
    return {
        "schema": "unrestricted-four-search-test-set-breakdown-v1",
        "counting_rule": {
            "primary_reporting": "report order5 and ALPS4141 separately",
            "search_execution": "4187 alpha-renaming/equality-symmetry representatives",
            "accepted_equivalence_classes": "a representative has a selected Judge-accepted certificate",
            "covered_original_records_via_equivalence": "all original source records in an accepted representative's frozen equivalence class",
            "receipt_boundary": "mapped duplicate records are coverage entries, not additional Judge receipts",
        },
        "order5": order5,
        "alps4141": alps,
        "cross_source_equivalence_classes": cross_source,
        "combined_execution_representatives": len(input_rows),
    }


def main() -> int:
    rows = read_jsonl(ROOT / "results" / "per_profile_results.jsonl")
    input_rows = read_jsonl(ROOT / "inputs" / "all_4187.jsonl")
    accepted_sets = json.loads(
        (ROOT / "results" / "accepted_sets.json").read_text(encoding="utf-8")
    )
    profiles = {}
    for profile in sorted({row["profile"] for row in rows}):
        selected = [row for row in rows if row["profile"] == profile]
        profiles[profile] = {
            "records": len(selected),
            "generation": dict(
                sorted(Counter(row["generation_status"] for row in selected).items())
            ),
            "judge": dict(
                sorted(Counter(row["judge_status"] for row in selected).items())
            ),
            "generated_unique_problems": len(
                {row["problem_id"] for row in selected if row["generation_status"] == "generated"}
            ),
            "accepted_unique_problems": len(
                {row["problem_id"] for row in selected if row["judge_status"] == "accepted"}
            ),
        }

    families = {
        name: set(problem_ids)
        for name, problem_ids in accepted_sets["families"].items()
    }
    union = set().union(*families.values())
    fluctuation = set(accepted_sets["trace_fluctuation_supplement_not_in_primary_union"])
    recomputed = {
        "schema": "unrestricted-four-search-recomputed-summary-v1",
        "public_profile_rows": len(rows),
        "profiles": profiles,
        "selected_family_counts": {name: len(values) for name, values in families.items()},
        "four_family_union": len(union),
        "trace_fluctuation_certificates": len(fluctuation),
        "trace_fluctuation_incremental_over_primary_union": len(fluctuation - union),
        "four_family_union_plus_trace_fluctuation": len(union | fluctuation),
        "test_sets": test_set_breakdown(input_rows, families),
    }
    target = ROOT / "results" / "recomputed_summary.json"
    target.write_text(
        json.dumps(recomputed, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    (ROOT / "results" / "test_set_breakdown.json").write_text(
        json.dumps(recomputed["test_sets"], ensure_ascii=False, indent=2, sort_keys=True)
        + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(recomputed, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
