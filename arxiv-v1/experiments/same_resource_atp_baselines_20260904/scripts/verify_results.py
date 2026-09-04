#!/usr/bin/env python3
"""Recompute structural invariants from the released compressed result rows."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

from independent_reparse import aggregate_status, reparse_attempt_details


TOOLS = ("vampire", "eprover", "twee_complete")
SOURCES = {"austin96": 96, "generality34": 34, "alps4141": 4141}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--experiment-root", type=Path, required=True)
    return parser.parse_args()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_gzip_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected object")
            rows.append(row)
    return rows


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> int:
    args = parse_args()
    root = args.experiment_root.resolve()
    atp = root / "results" / "atp"
    summary = json.loads((atp / "summary.json").read_text(encoding="utf-8"))
    input_ids = [
        json.loads(line)["id"]
        for line in (root / "inputs" / "combined_4271.jsonl").read_text(
            encoding="utf-8"
        ).splitlines()
        if line.strip()
    ]
    require(len(input_ids) == 4271 and len(set(input_ids)) == 4271, "input ID audit")

    inner_manifest = json.loads((atp / "manifest.json").read_text(encoding="utf-8"))
    for entry in inner_manifest["files"]:
        path = atp / entry["path"]
        require(path.is_file(), f"missing inner-manifest file: {entry['path']}")
        require(path.stat().st_size == entry["bytes"], f"size mismatch: {entry['path']}")
        require(sha256(path) == entry["sha256"], f"hash mismatch: {entry['path']}")

    all_rows: dict[str, list[dict[str, Any]]] = {}
    for tool in TOOLS:
        rows = read_gzip_jsonl(atp / tool / "per_problem_results.jsonl.gz")
        all_rows[tool] = rows
        require(len(rows) == 4271, f"{tool}: row count")
        require([row["record_id"] for row in rows] == input_ids, f"{tool}: input order")
        require(len({row["record_id"] for row in rows}) == 4271, f"{tool}: unique IDs")
        require(
            dict(sorted(Counter(row["status"] for row in rows).items()))
            == summary["tools"][tool]["status_counts"],
            f"{tool}: status counts",
        )
        require(
            all(
                "zlib_b64" not in stream
                for row in rows
                for attempt in row.get("attempts", [])
                for stream in (attempt.get("stdout", {}), attempt.get("stderr", {}))
            ),
            f"{tool}: sanitized stream payload",
        )
        evidence = read_gzip_jsonl(atp / tool / "status_evidence_streams.jsonl.gz")
        expected_evidence_ids = {
            row["record_id"]
            for row in rows
            if row["status"] in {"theorem", "counter_satisfiable"}
            or row.get("raw_counter_satisfiable_seen")
        }
        require(
            {row["record_id"] for row in evidence} == expected_evidence_ids,
            f"{tool}: status-evidence membership",
        )
        require(
            len(evidence)
            == summary["tools"][tool]["public_artifacts"]["status_evidence_streams"]["rows"],
            f"{tool}: status-evidence count",
        )
        evidence_by_id = {row["record_id"]: row for row in evidence}
        require(len(evidence_by_id) == len(evidence), f"{tool}: duplicate evidence ID")
        sanitized_by_id = {row["record_id"]: row for row in rows}
        for record_id, evidence_row in evidence_by_id.items():
            statuses = []
            for attempt in evidence_row["attempts"]:
                details = reparse_attempt_details(tool, attempt)
                statuses.append(details["status"])
                for field, value in details.items():
                    require(attempt.get(field) == value, f"{tool}/{record_id}: {field}")
            require(
                aggregate_status(statuses) == evidence_row["status"],
                f"{tool}/{record_id}: reparsed aggregate",
            )
            require(
                evidence_row["status"] == sanitized_by_id[record_id]["status"],
                f"{tool}/{record_id}: evidence/sanitized status",
            )
        if tool in {"vampire", "eprover"}:
            require(
                all(not row.get("counter_satisfiable_trusted") for row in rows),
                f"{tool}: no trusted counter allowed by frozen protocol",
            )
            require(
                all(row["status"] != "counter_satisfiable" for row in rows),
                f"{tool}: scientific counter status must be empty",
            )
        else:
            require(
                all(
                    bool(row.get("counter_satisfiable_trusted"))
                    == (row["status"] == "counter_satisfiable")
                    == (row.get("scientific_verdict") == "AUSTIN")
                    for row in rows
                ),
                f"{tool}: trusted counter fields must be equivalent",
            )

    for source, expected in SOURCES.items():
        source_ids = {
            row["record_id"]
            for row in all_rows[TOOLS[0]]
            if row["paper_dataset"] == source
        }
        require(len(source_ids) == expected, f"{source}: source denominator")
        for tool in TOOLS:
            split_rows = read_gzip_jsonl(
                atp / "by_source" / source / f"{tool}_per_problem_results.jsonl.gz"
            )
            require(len(split_rows) == expected, f"{source}/{tool}: split count")
            require(
                {row["record_id"] for row in split_rows} == source_ids,
                f"{source}/{tool}: split membership",
            )

    with (atp / "deduplicated" / "exact_unique_problem_statuses.csv").open(
        "r", encoding="utf-8", newline=""
    ) as handle:
        exact_rows = list(csv.DictReader(handle))
    with (atp / "deduplicated" / "alpha_unique_problem_statuses.csv").open(
        "r", encoding="utf-8", newline=""
    ) as handle:
        alpha_rows = list(csv.DictReader(handle))
    require(len(exact_rows) == 4188, "exact unique problem count")
    require(len(alpha_rows) == 4187, "alpha unique problem count")
    require(sum(row["theorem_any"] == "True" for row in exact_rows) == 94, "exact theorem union")
    require(
        sum(row["counter_satisfiable_any"] == "True" for row in exact_rows) == 18,
        "exact counter union",
    )
    require(sum(row["scientific_conflict"] == "True" for row in exact_rows) == 0, "exact conflict")
    require(sum(row["theorem_any"] == "True" for row in alpha_rows) == 94, "alpha theorem union")
    require(
        sum(row["counter_satisfiable_any"] == "True" for row in alpha_rows) == 18,
        "alpha counter union",
    )
    require(sum(row["scientific_conflict"] == "True" for row in alpha_rows) == 0, "alpha conflict")

    primary = summary["primary_benchmark_summaries"]
    require(primary["order5_130"]["records"] == 130, "order5 denominator")
    require(
        primary["order5_130"]["record_id_unions"]
        == {"counter_satisfiable": 18, "theorem": 2},
        "order5 decisive unions",
    )
    require(primary["alps4141"]["records"] == 4141, "ALPS denominator")
    require(
        primary["alps4141"]["record_id_unions"]
        == {"counter_satisfiable": 4, "theorem": 94},
        "ALPS decisive unions",
    )

    input_overlap = json.loads(
        (root / "results" / "input_overlap" / "summary.json").read_text(encoding="utf-8")
    )
    require(input_overlap["exact_directed_implication"]["unique_problems"] == 4188, "overlap exact")
    require(
        input_overlap["alpha_renaming_and_equation_symmetry"]["unique_problems"]
        == 4187,
        "overlap alpha",
    )
    alps_coverage = json.loads(
        (root / "results" / "alps_etp_coverage" / "summary.json").read_text(
            encoding="utf-8"
        )
    )
    require(alps_coverage["totals"]["in_alps_final_status"] == 115, "ALPS final coverage")
    require(alps_coverage["totals"]["in_alps_evaluation_pool"] == 83, "ALPS pool overlap")

    print(
        json.dumps(
            {
                "tool_problem_rows": 12813,
                "exact_unique_problems": 4188,
                "alpha_unique_problems": 4187,
                "theorem_union": 94,
                "counter_satisfiable_union": 18,
                "scientific_conflicts": 0,
                "verified": True,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
