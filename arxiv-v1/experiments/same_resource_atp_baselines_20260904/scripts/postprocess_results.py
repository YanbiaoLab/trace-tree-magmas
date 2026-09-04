#!/usr/bin/env python3
"""Validate, sanitize, and summarize a completed same-resource ATP run.

The private raw files contain compressed copies of every solver stream.  The
public artifact keeps stream hashes and byte counts for every problem.  It
also keeps complete compressed streams for every decisive result, every raw
counter-status row (including deliberately nondecisive ones), and all three
tools on the frozen 28-problem focus set.  This makes the Git artifact
auditable without committing hundreds of megabytes of unrelated timeout
output.
"""

from __future__ import annotations

import argparse
import copy
import csv
import gzip
import hashlib
import json
import os
import re
import shutil
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable

from audit_input_overlap import alpha_equivalence_key, exact_key
from independent_reparse import audit_file as independent_audit


TOOLS = ("vampire", "eprover", "twee_complete")
SOURCE_PRIORITY = ("generality34", "austin96", "alps4141")
DECISIVE = frozenset(("theorem", "counter_satisfiable"))
PRIVATE_PATTERNS = (
    re.compile(rb"sandbox_id", re.IGNORECASE),
    re.compile(
        rb"[\"']sandbox_id[\"']\s*:\s*[\"'][A-Za-z0-9_-]{8,}[\"']",
        re.IGNORECASE,
    ),
    re.compile(rb"default--math-distill", re.IGNORECASE),
    re.compile(rb"(?:api[_-]?key|E2B_API_KEY)", re.IGNORECASE),
    re.compile(rb"(?:^|[^A-Za-z0-9])sk-[A-Za-z0-9_-]{8,}"),
    re.compile(rb"[A-Za-z]:\\(?:Users|Desktop)\\", re.IGNORECASE),
    re.compile(rb"(?:^|[/\\])\.env(?:$|[^A-Za-z0-9_])", re.IGNORECASE),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument(
        "--raw-root",
        type=Path,
        required=True,
        help="Directory with TOOL/raw_results.jsonl for each configured tool.",
    )
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{line_number}: expected a JSON object")
            rows.append(value)
    return rows


def require_unique_ids(rows: Iterable[dict[str, Any]], field: str, label: str) -> list[str]:
    values = [str(row[field]) for row in rows]
    duplicates = sorted(key for key, count in Counter(values).items() if count > 1)
    if duplicates:
        raise ValueError(f"{label}: duplicate {field}: {duplicates[:5]}")
    return values


def strip_stream_payloads(row: dict[str, Any]) -> dict[str, Any]:
    public = copy.deepcopy(row)
    for attempt in public.get("attempts", []):
        for stream_name in ("stdout", "stderr"):
            stream = attempt.get(stream_name)
            if isinstance(stream, dict):
                stream.pop("zlib_b64", None)
                stream["payload_retained"] = False
    return public


def stream_evidence_record(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": "same-resource-atp-status-evidence-stream-v1",
        "tool": row["tool"],
        "record_id": row["record_id"],
        "paper_dataset": row["paper_dataset"],
        "problem_sha256": row["problem_sha256"],
        "status": row["status"],
        "winning_attempt_index": row.get("winning_attempt_index"),
        "attempts": row.get("attempts", []),
    }


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def write_deterministic_gzip_jsonl(
    path: Path, rows: Iterable[dict[str, Any]]
) -> tuple[int, int]:
    path.parent.mkdir(parents=True, exist_ok=True)
    row_count = 0
    uncompressed_bytes = 0
    with path.open("wb") as raw_handle:
        with gzip.GzipFile(
            filename="", fileobj=raw_handle, mode="wb", compresslevel=9, mtime=0
        ) as gzip_handle:
            for row in rows:
                payload = canonical_bytes(row)
                gzip_handle.write(payload)
                row_count += 1
                uncompressed_bytes += len(payload)
    return row_count, uncompressed_bytes


def counter_tree(rows: list[dict[str, Any]], key: str) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for group_value in sorted({str(row[key]) for row in rows}):
        statuses = Counter(
            str(row["status"]) for row in rows if str(row[key]) == group_value
        )
        result[group_value] = dict(sorted(statuses.items()))
    return result


def capability_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    fields = (
        "source_implication_proved",
        "complete_tstp_proof_emitted",
        "explicit_model_emitted",
        "explicit_infinite_carrier_emitted",
        "independent_certificate_accepted",
    )
    result = {field: sum(bool(row.get(field)) for row in rows) for field in fields}
    result["judge_calls"] = sum(int(row.get("judge_calls", 0)) for row in rows)
    return result


def distribution(values: list[float]) -> dict[str, float | int | None]:
    if not values:
        return {"count": 0, "mean": None, "p50": None, "p90": None, "p95": None, "p99": None, "max": None}
    ordered = sorted(float(value) for value in values)

    def percentile(fraction: float) -> float:
        position = (len(ordered) - 1) * fraction
        lower = int(position)
        upper = min(lower + 1, len(ordered) - 1)
        weight = position - lower
        return ordered[lower] * (1.0 - weight) + ordered[upper] * weight

    return {
        "count": len(ordered),
        "mean": round(sum(ordered) / len(ordered), 6),
        "p50": round(percentile(0.50), 6),
        "p90": round(percentile(0.90), 6),
        "p95": round(percentile(0.95), 6),
        "p99": round(percentile(0.99), 6),
        "max": round(max(ordered), 6),
    }


def resource_statistics(rows: list[dict[str, Any]]) -> dict[str, Any]:
    def group(selected: list[dict[str, Any]]) -> dict[str, Any]:
        solver = [float(row["solver_wall_seconds"]) for row in selected]
        cleanup = [float(row["cleanup_seconds"]) for row in selected]
        overall = [float(row["elapsed_seconds"]) for row in selected]
        wrapper = [max(0.0, overall[index] - solver[index] - cleanup[index]) for index in range(len(selected))]
        peak = [
            float(max((attempt["peak_process_group_rss_bytes"] for attempt in row.get("attempts", [])), default=0))
            for row in selected
        ]
        return {
            "solver_wall_seconds": distribution(solver),
            "cleanup_seconds": distribution(cleanup),
            "wrapper_non_solver_seconds": distribution(wrapper),
            "overall_wall_seconds": distribution(overall),
            "peak_process_group_rss_bytes": distribution(peak),
        }

    decisive = [row for row in rows if row["status"] in DECISIVE]
    nondecisive = [row for row in rows if row["status"] not in DECISIVE]
    return {
        "all_problems": group(rows),
        "decisive_problems": group(decisive),
        "nondecisive_problems": group(nondecisive),
        "memory_definition": {
            "metric": "sampled aggregate process-group RSS",
            "scope": "complete solver process group",
            "sample_interval_seconds": 0.05,
            "internal_limit_mib": 2000,
            "sandbox_limit_mib": 2048,
            "limitation": "A transient peak between samples can be missed; cgroup OOM counters and a near-limit SIGKILL fallback classify such kills.",
        },
    }


def inspect_public_bytes(label: str, payload: bytes) -> None:
    for pattern in PRIVATE_PATTERNS:
        if pattern.search(payload):
            raise ValueError(f"private-information safety check failed for {label}")


def write_status_csv(
    path: Path,
    ids: list[str],
    input_by_id: dict[str, dict[str, Any]],
    rows_by_tool: dict[str, dict[str, dict[str, Any]]],
) -> None:
    fieldnames = [
        "record_id",
        "paper_dataset",
        "original_problem_id",
        "source_eq_id",
        "target_eq_id",
        *TOOLS,
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for record_id in ids:
            source = input_by_id[record_id]
            writer.writerow(
                {
                    "record_id": record_id,
                    "paper_dataset": source.get("paper_dataset", ""),
                    "original_problem_id": source.get("original_problem_id", ""),
                    "source_eq_id": source.get("source_eq_id", ""),
                    "target_eq_id": source.get("target_eq_id", ""),
                    **{
                        tool: rows_by_tool[tool][record_id]["status"] for tool in TOOLS
                    },
                }
            )


def make_equivalence_groups(
    input_rows: list[dict[str, Any]], key_function: Any
) -> list[list[str]]:
    groups: dict[str, list[str]] = defaultdict(list)
    for row in input_rows:
        groups[str(key_function(row))].append(str(row["id"]))
    return [groups[key] for key in sorted(groups)]


def scientific_group_counts(
    groups: list[list[str]], rows_by_tool: dict[str, dict[str, dict[str, Any]]]
) -> dict[str, int]:
    theorem = 0
    counter = 0
    conflict = 0
    for members in groups:
        statuses = {
            str(rows_by_tool[tool][record_id]["status"])
            for tool in TOOLS
            for record_id in members
        }
        has_theorem = "theorem" in statuses
        has_counter = "counter_satisfiable" in statuses
        theorem += has_theorem
        counter += has_counter
        conflict += has_theorem and has_counter
    return {
        "problems": len(groups),
        "theorem": theorem,
        "counter_satisfiable": counter,
        "theorem_and_counter_satisfiable_conflicts": conflict,
    }


def write_unique_status_csv(
    path: Path,
    equivalence: str,
    groups: list[list[str]],
    input_by_id: dict[str, dict[str, Any]],
    rows_by_tool: dict[str, dict[str, dict[str, Any]]],
) -> None:
    priority = {source: index for index, source in enumerate(SOURCE_PRIORITY)}
    input_position = {record_id: index for index, record_id in enumerate(input_by_id)}
    columns = [
        "equivalence_group_id",
        "representative_record_id",
        "member_count",
        "provenance_sources",
        "member_record_ids",
        *[f"{tool}_statuses" for tool in TOOLS],
        "theorem_any",
        "counter_satisfiable_any",
        "scientific_conflict",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=columns, lineterminator="\n")
        writer.writeheader()
        for members in groups:
            representative = min(
                members,
                key=lambda record_id: (
                    priority.get(
                        str(input_by_id[record_id]["paper_dataset"]), len(priority)
                    ),
                    input_position[record_id],
                ),
            )
            all_statuses = {
                str(rows_by_tool[tool][record_id]["status"])
                for tool in TOOLS
                for record_id in members
            }
            group_digest = hashlib.sha256(
                (equivalence + "\0" + "\0".join(sorted(members))).encode("utf-8")
            ).hexdigest()[:16]
            writer.writerow(
                {
                    "equivalence_group_id": f"{equivalence}_{group_digest}",
                    "representative_record_id": representative,
                    "member_count": len(members),
                    "provenance_sources": "+".join(
                        sorted(
                            {
                                str(input_by_id[record_id]["paper_dataset"])
                                for record_id in members
                            }
                        )
                    ),
                    "member_record_ids": " | ".join(members),
                    **{
                        f"{tool}_statuses": "+".join(
                            sorted(
                                {
                                    str(rows_by_tool[tool][record_id]["status"])
                                    for record_id in members
                                }
                            )
                        )
                        for tool in TOOLS
                    },
                    "theorem_any": "theorem" in all_statuses,
                    "counter_satisfiable_any": "counter_satisfiable" in all_statuses,
                    "scientific_conflict": (
                        "theorem" in all_statuses
                        and "counter_satisfiable" in all_statuses
                    ),
                }
            )


def main() -> int:
    args = parse_args()
    input_path = args.input.resolve()
    raw_root = args.raw_root.resolve()
    output_path = args.output.resolve()

    input_rows = read_jsonl(input_path)
    input_ids = require_unique_ids(input_rows, "id", "input")
    input_by_id = {str(row["id"]): row for row in input_rows}
    expected_set = set(input_ids)
    focus_path = input_path.parent / "focus28_ids.txt"
    focus_ids = {line.strip() for line in focus_path.read_text(encoding="utf-8").splitlines() if line.strip()}
    if len(focus_ids) != 28 or not focus_ids <= expected_set:
        raise ValueError("focus28 ID audit failed")
    exact_groups = make_equivalence_groups(input_rows, exact_key)
    alpha_groups = make_equivalence_groups(input_rows, alpha_equivalence_key)

    raw_paths = {tool: raw_root / tool / "raw_results.jsonl" for tool in TOOLS}
    for path in raw_paths.values():
        if not path.is_file():
            raise FileNotFoundError(path)

    tool_rows: dict[str, list[dict[str, Any]]] = {}
    rows_by_tool: dict[str, dict[str, dict[str, Any]]] = {}
    raw_order_matches_input: dict[str, bool] = {}
    for tool, path in raw_paths.items():
        independent_audit(path, input_path)
        rows = read_jsonl(path)
        ids = require_unique_ids(rows, "record_id", tool)
        actual_set = set(ids)
        if actual_set != expected_set:
            missing = sorted(expected_set - actual_set)
            extra = sorted(actual_set - expected_set)
            raise ValueError(f"{tool}: missing={missing[:5]} extra={extra[:5]}")
        raw_order_matches_input[tool] = ids == input_ids
        row_index = {str(row["record_id"]): row for row in rows}
        rows = [row_index[record_id] for record_id in input_ids]
        if any(row.get("tool") != tool for row in rows):
            raise ValueError(f"{tool}: mismatched tool label")
        for row in rows:
            record_id = str(row["record_id"])
            if row.get("paper_dataset") != input_by_id[record_id].get("paper_dataset"):
                raise ValueError(f"{tool}:{record_id}: paper_dataset mismatch")
        tool_rows[tool] = rows
        rows_by_tool[tool] = {str(row["record_id"]): row for row in rows}

    theorem_ids = [
        record_id
        for record_id in input_ids
        if any(rows_by_tool[tool][record_id]["status"] == "theorem" for tool in TOOLS)
    ]
    counter_ids = [
        record_id
        for record_id in input_ids
        if any(
            rows_by_tool[tool][record_id]["status"] == "counter_satisfiable"
            for tool in TOOLS
        )
    ]
    scientific_conflicts = sorted(set(theorem_ids) & set(counter_ids))
    if scientific_conflicts:
        raise ValueError(
            "theorem/counter_satisfiable cross-tool conflicts: "
            + ", ".join(scientific_conflicts[:10])
        )
    exact_scientific_counts = scientific_group_counts(exact_groups, rows_by_tool)
    alpha_scientific_counts = scientific_group_counts(alpha_groups, rows_by_tool)
    if (
        exact_scientific_counts["theorem_and_counter_satisfiable_conflicts"]
        or alpha_scientific_counts["theorem_and_counter_satisfiable_conflicts"]
    ):
        raise ValueError("theorem/counter_satisfiable conflict after problem deduplication")

    output_parent = output_path.parent
    output_parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{output_path.name}.tmp-", dir=output_parent))
    summaries: dict[str, dict[str, Any]] = {}
    try:
        for tool in TOOLS:
            rows = tool_rows[tool]
            tool_dir = temporary / tool
            public_results_path = tool_dir / "per_problem_results.jsonl.gz"
            evidence_path = tool_dir / "status_evidence_streams.jsonl.gz"
            focus_path = tool_dir / "focus28_streams.jsonl.gz"
            sanitized_rows = [strip_stream_payloads(row) for row in rows]
            public_count, public_uncompressed_bytes = write_deterministic_gzip_jsonl(
                public_results_path, sanitized_rows
            )
            evidence_rows = [
                stream_evidence_record(row)
                for row in rows
                if row["status"] in DECISIVE or row.get("raw_counter_satisfiable_seen")
            ]
            evidence_count, evidence_uncompressed_bytes = write_deterministic_gzip_jsonl(
                evidence_path, evidence_rows
            )
            focus_rows = [stream_evidence_record(row) for row in rows if row["record_id"] in focus_ids]
            focus_count, focus_uncompressed_bytes = write_deterministic_gzip_jsonl(
                focus_path, focus_rows
            )
            if focus_count != 28:
                raise ValueError(f"{tool}: focus28 stream count")

            summary = {
                "schema": "same-resource-atp-tool-summary-v1",
                "tool": tool,
                "input": {
                    "records": len(input_rows),
                    "unique_ids": len(expected_set),
                    "missing_ids": 0,
                    "extra_ids": 0,
                    "duplicate_ids": 0,
                    "raw_order_matches_input": raw_order_matches_input[tool],
                    "public_order_matches_input": True,
                },
                "status_counts": dict(sorted(Counter(row["status"] for row in rows).items())),
                "raw_counter_status_rows": sum(
                    bool(row.get("raw_counter_satisfiable_seen")) for row in rows
                ),
                "trusted_counter_satisfiable_rows": sum(
                    bool(row.get("counter_satisfiable_trusted")) for row in rows
                ),
                "status_counts_by_dataset": counter_tree(rows, "paper_dataset"),
                "capability_counts": capability_counts(rows),
                "resource_statistics": resource_statistics(rows),
                "raw_source": {
                    "bytes": raw_paths[tool].stat().st_size,
                    "sha256": file_sha256(raw_paths[tool]),
                    "committed": False,
                    "note": "The private controller file is not committed. Public rows retain every stream hash and byte count; full payloads are retained for all decisive rows, every raw counter-status row, and the frozen 28-problem focus subset.",
                },
                "public_artifacts": {
                    "per_problem_results": {
                        "bytes": public_results_path.stat().st_size,
                        "sha256": file_sha256(public_results_path),
                        "rows": public_count,
                        "uncompressed_bytes": public_uncompressed_bytes,
                    },
                    "status_evidence_streams": {
                        "bytes": evidence_path.stat().st_size,
                        "sha256": file_sha256(evidence_path),
                        "rows": evidence_count,
                        "uncompressed_bytes": evidence_uncompressed_bytes,
                    },
                    "focus28_streams": {
                        "bytes": focus_path.stat().st_size,
                        "sha256": file_sha256(focus_path),
                        "rows": focus_count,
                        "uncompressed_bytes": focus_uncompressed_bytes,
                    },
                },
            }
            write_json(tool_dir / "summary.json", summary)
            summaries[tool] = summary

        source_summaries: dict[str, Any] = {}
        for source in sorted({str(row["paper_dataset"]) for row in input_rows}):
            source_ids = [
                record_id
                for record_id in input_ids
                if str(input_by_id[record_id]["paper_dataset"]) == source
            ]
            source_dir = temporary / "by_source" / source
            tool_source_summaries: dict[str, Any] = {}
            for tool in TOOLS:
                selected_rows = [rows_by_tool[tool][record_id] for record_id in source_ids]
                selected_public = [strip_stream_payloads(row) for row in selected_rows]
                selected_path = source_dir / f"{tool}_per_problem_results.jsonl.gz"
                selected_count, selected_uncompressed_bytes = write_deterministic_gzip_jsonl(
                    selected_path, selected_public
                )
                tool_source_summaries[tool] = {
                    "records": selected_count,
                    "status_counts": dict(
                        sorted(Counter(row["status"] for row in selected_rows).items())
                    ),
                    "bytes": selected_path.stat().st_size,
                    "uncompressed_bytes": selected_uncompressed_bytes,
                    "sha256": file_sha256(selected_path),
                }
            source_theorems = [
                record_id
                for record_id in source_ids
                if any(
                    rows_by_tool[tool][record_id]["status"] == "theorem"
                    for tool in TOOLS
                )
            ]
            source_counters = [
                record_id
                for record_id in source_ids
                if any(
                    rows_by_tool[tool][record_id]["status"]
                    == "counter_satisfiable"
                    for tool in TOOLS
                )
            ]
            source_summary = {
                "schema": "same-resource-atp-source-summary-v1",
                "paper_dataset": source,
                "records": len(source_ids),
                "tool_results": tool_source_summaries,
                "record_id_unions": {
                    "theorem": len(source_theorems),
                    "counter_satisfiable": len(source_counters),
                    "theorem_and_counter_satisfiable_conflicts": len(
                        set(source_theorems) & set(source_counters)
                    ),
                },
            }
            write_json(source_dir / "summary.json", source_summary)
            source_summaries[source] = source_summary

        primary_benchmarks: dict[str, Any] = {}
        for benchmark, source_names in {
            "order5_130": {"austin96", "generality34"},
            "alps4141": {"alps4141"},
        }.items():
            benchmark_ids = [
                record_id
                for record_id in input_ids
                if str(input_by_id[record_id]["paper_dataset"]) in source_names
            ]
            if len(benchmark_ids) != (130 if benchmark == "order5_130" else 4141):
                raise ValueError(f"{benchmark}: frozen benchmark size mismatch")
            primary_benchmarks[benchmark] = {
                "records": len(benchmark_ids),
                "tools": {
                    tool: {
                        "status_counts": dict(
                            sorted(
                                Counter(
                                    rows_by_tool[tool][record_id]["status"]
                                    for record_id in benchmark_ids
                                ).items()
                            )
                        ),
                        "raw_counter_status_rows": sum(
                            bool(
                                rows_by_tool[tool][record_id].get(
                                    "raw_counter_satisfiable_seen"
                                )
                            )
                            for record_id in benchmark_ids
                        ),
                    }
                    for tool in TOOLS
                },
                "record_id_unions": {
                    "theorem": sum(
                        any(
                            rows_by_tool[tool][record_id]["status"] == "theorem"
                            for tool in TOOLS
                        )
                        for record_id in benchmark_ids
                    ),
                    "counter_satisfiable": sum(
                        any(
                            rows_by_tool[tool][record_id]["status"]
                            == "counter_satisfiable"
                            for tool in TOOLS
                        )
                        for record_id in benchmark_ids
                    ),
                },
            }

        theorem_status_csv = temporary / "theorem_statuses.csv"
        counter_status_csv = temporary / "counter_satisfiable_statuses.csv"
        write_status_csv(theorem_status_csv, theorem_ids, input_by_id, rows_by_tool)
        write_status_csv(counter_status_csv, counter_ids, input_by_id, rows_by_tool)
        write_unique_status_csv(
            temporary / "deduplicated" / "exact_unique_problem_statuses.csv",
            "exact",
            exact_groups,
            input_by_id,
            rows_by_tool,
        )
        write_unique_status_csv(
            temporary / "deduplicated" / "alpha_unique_problem_statuses.csv",
            "alpha",
            alpha_groups,
            input_by_id,
            rows_by_tool,
        )

        proof_membership = Counter()
        counter_membership = Counter()
        for record_id in input_ids:
            proving = tuple(
                tool for tool in TOOLS if rows_by_tool[tool][record_id]["status"] == "theorem"
            )
            countering = tuple(
                tool
                for tool in TOOLS
                if rows_by_tool[tool][record_id]["status"] == "counter_satisfiable"
            )
            if proving:
                proof_membership["+".join(proving)] += 1
            if countering:
                counter_membership["+".join(countering)] += 1

        global_summary = {
            "schema": "same-resource-atp-summary-v1",
            "input": {
                "path": "inputs/combined_4271.jsonl",
                "records": len(input_rows),
                "sha256": file_sha256(input_path),
            },
            "tools": summaries,
            "record_id_unions": {
                "theorem": len(theorem_ids),
                "counter_satisfiable": len(counter_ids),
                "theorem_and_counter_satisfiable_conflicts": len(scientific_conflicts),
                "explicit_model_emitted": len(
                    {
                        row["record_id"]
                        for rows in tool_rows.values()
                        for row in rows
                        if row.get("explicit_model_emitted")
                    }
                ),
                "independent_certificate_accepted": len(
                    {
                        row["record_id"]
                        for rows in tool_rows.values()
                        for row in rows
                        if row.get("independent_certificate_accepted")
                    }
                ),
            },
            "unique_problem_unions": {
                "exact_directed_implication": exact_scientific_counts,
                "alpha_renaming_and_equation_symmetry": alpha_scientific_counts,
            },
            "source_summaries": source_summaries,
            "primary_benchmark_summaries": primary_benchmarks,
            "reporting_rule": "Report order5_130 and alps4141 separately; the 4271-row concatenation and its deduplications are audit views only because sources overlap.",
            "theorem_tool_membership": dict(sorted(proof_membership.items())),
            "counter_satisfiable_tool_membership": dict(sorted(counter_membership.items())),
            "judge_boundary": {
                "judge_calls": sum(
                    int(row.get("judge_calls", 0))
                    for rows in tool_rows.values()
                    for row in rows
                ),
                "judge_v3_applicable": False,
                "reason": "ATP proof/model text is not a TraceTree certificate. The remote Judge-v3 canary is a separate artifact.",
            },
            "sanitization": {
                "all_stream_hashes_and_sizes_retained": True,
                "all_decisive_stream_payloads_retained": True,
                "all_raw_counter_status_stream_payloads_retained": True,
                "all_focus28_stream_payloads_retained": True,
                "focus28_tool_rows_with_full_streams": 84,
                "other_nondecisive_stream_payloads_retained": False,
                "private_pattern_hits": 0,
            },
        }
        write_json(temporary / "summary.json", global_summary)

        overlap_audit = {
            "schema": "same-resource-atp-overlap-audit-v1",
            "input_equivalence": {
                "record_ids": len(input_ids),
                "exact_directed_implications": len(exact_groups),
                "alpha_renaming_and_equation_symmetry": len(alpha_groups),
                "exact_redundant_records": len(input_ids) - len(exact_groups),
                "alpha_redundant_records": len(input_ids) - len(alpha_groups),
            },
            "execution": {
                "all_tools_fresh_full_run": True,
                "twee_each_reached_configuration_has_full_15_second_allowance": True,
                "memory_protocol": "uniform-process-tree-rss-v2",
            },
            "scientific_conflicts": scientific_conflicts,
        }
        write_json(temporary / "overlap_provenance.json", overlap_audit)

        # Scan both plain public files and the uncompressed decisive JSON objects.
        for path in temporary.rglob("*"):
            if path.is_file() and path.suffix != ".gz":
                inspect_public_bytes(path.relative_to(temporary).as_posix(), path.read_bytes())
        for tool in TOOLS:
            for row in tool_rows[tool]:
                inspect_public_bytes(
                    f"{tool}:{row['record_id']}:sanitized",
                    canonical_bytes(strip_stream_payloads(row)),
                )
                if row["status"] in DECISIVE or row.get("raw_counter_satisfiable_seen"):
                    inspect_public_bytes(
                        f"{tool}:{row['record_id']}", canonical_bytes(stream_evidence_record(row))
                    )

        manifest_entries = []
        for path in sorted(p for p in temporary.rglob("*") if p.is_file()):
            relative = path.relative_to(temporary).as_posix()
            manifest_entries.append(
                {"path": relative, "bytes": path.stat().st_size, "sha256": file_sha256(path)}
            )
        write_json(
            temporary / "manifest.json",
            {
                "schema": "same-resource-atp-public-manifest-v1",
                "files": manifest_entries,
            },
        )

        if output_path.exists():
            raise FileExistsError(
                f"refusing to overwrite existing output directory: {output_path}"
            )
        os.replace(temporary, output_path)
    except Exception:
        shutil.rmtree(temporary, ignore_errors=True)
        raise

    print(
        json.dumps(
            {
                "output": str(output_path),
                "input_records": len(input_rows),
                "theorem_union": len(theorem_ids),
                "counter_satisfiable_union": len(counter_ids),
                "scientific_conflicts": len(scientific_conflicts),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
