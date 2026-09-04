#!/usr/bin/env python3
"""Audit cross-source duplicate implication problems in a frozen JSONL input."""

from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable


SOURCE_PRIORITY = ("generality34", "austin96", "alps4141")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|[()*=]")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    return parser.parse_args()


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected a JSON object")
            rows.append(row)
    return rows


class TermParser:
    def __init__(self, text: str) -> None:
        self.tokens = TOKEN_RE.findall(text)
        compact = re.sub(r"\s+", "", text)
        if "".join(self.tokens) != compact:
            raise ValueError(f"unsupported equation syntax: {text!r}")
        self.position = 0

    def peek(self) -> str | None:
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def take(self, expected: str | None = None) -> str:
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise ValueError(f"expected {expected!r}, got {token!r}")
        self.position += 1
        return token

    def factor(self) -> tuple[Any, ...]:
        if self.peek() == "(":
            self.take("(")
            left = self.term()
            self.take(")")
            return left
        token = self.take()
        if token in ("*", "=", ")"):
            raise ValueError(f"expected variable, got {token!r}")
        return ("var", token)

    def term(self) -> tuple[Any, ...]:
        # Parentheses in the source fully determine non-left-associated parts;
        # an unparenthesized outer product is parsed with the usual left fold.
        value = self.factor()
        while self.peek() == "*":
            self.take("*")
            value = ("*", value, self.factor())
        return value

    def equation(self) -> tuple[tuple[Any, ...], tuple[Any, ...]]:
        left = self.term()
        self.take("=")
        right = self.term()
        if self.peek() is not None:
            raise ValueError(f"unexpected trailing token {self.peek()!r}")
        return left, right


def variables(term: tuple[Any, ...]) -> set[str]:
    if term[0] == "var":
        return {str(term[1])}
    return variables(term[1]) | variables(term[2])


def render(term: tuple[Any, ...], mapping: dict[str, str]) -> str:
    if term[0] == "var":
        return mapping[str(term[1])]
    return f"({render(term[1], mapping)}*{render(term[2], mapping)})"


def exact_key(row: dict[str, Any]) -> str:
    return (
        re.sub(r"\s+", "", str(row["equation1"]))
        + "=>"
        + re.sub(r"\s+", "", str(row["equation2"]))
    )


def alpha_equivalence_key(row: dict[str, Any]) -> str:
    premise = TermParser(str(row["equation1"])).equation()
    conclusion = TermParser(str(row["equation2"])).equation()
    names = sorted(
        variables(premise[0])
        | variables(premise[1])
        | variables(conclusion[0])
        | variables(conclusion[1])
    )
    canonical_names = [f"v{index}" for index in range(len(names))]
    candidates: list[str] = []
    for assigned in itertools.permutations(canonical_names):
        mapping = dict(zip(names, assigned))
        premise_lr = f"{render(premise[0], mapping)}={render(premise[1], mapping)}"
        premise_rl = f"{render(premise[1], mapping)}={render(premise[0], mapping)}"
        conclusion_lr = f"{render(conclusion[0], mapping)}={render(conclusion[1], mapping)}"
        conclusion_rl = f"{render(conclusion[1], mapping)}={render(conclusion[0], mapping)}"
        for premise_form in (premise_lr, premise_rl):
            for conclusion_form in (conclusion_lr, conclusion_rl):
                candidates.append(f"{premise_form}=>{conclusion_form}")
    return min(candidates)


def grouped(rows: Iterable[dict[str, Any]], key_name: str) -> dict[str, list[dict[str, Any]]]:
    result: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        result[str(row[key_name])].append(row)
    return dict(result)


def pair_counts(groups: Iterable[list[dict[str, Any]]]) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for group in groups:
        sources = sorted({str(row["paper_dataset"]) for row in group})
        if len(sources) > 1:
            counts[" & ".join(sources)] += 1
    return dict(sorted(counts.items()))


def main() -> int:
    args = parse_args()
    rows = read_jsonl(args.input)
    ids = [str(row["id"]) for row in rows]
    duplicate_ids = [key for key, count in Counter(ids).items() if count > 1]
    if duplicate_ids:
        raise ValueError(f"duplicate record IDs: {duplicate_ids[:5]}")

    enriched: list[dict[str, Any]] = []
    for row in rows:
        value = dict(row)
        value["_exact_key"] = exact_key(row)
        value["_alpha_key"] = alpha_equivalence_key(row)
        enriched.append(value)

    exact_groups = grouped(enriched, "_exact_key")
    alpha_groups = grouped(enriched, "_alpha_key")
    exact_duplicates = [group for group in exact_groups.values() if len(group) > 1]
    alpha_duplicates = [group for group in alpha_groups.values() if len(group) > 1]
    exact_cross = [
        group
        for group in exact_duplicates
        if len({str(row["paper_dataset"]) for row in group}) > 1
    ]
    alpha_cross = [
        group
        for group in alpha_duplicates
        if len({str(row["paper_dataset"]) for row in group}) > 1
    ]

    exact_keys_by_alpha: dict[str, set[str]] = defaultdict(set)
    for row in enriched:
        exact_keys_by_alpha[str(row["_alpha_key"])].add(str(row["_exact_key"]))
    alpha_only_group_count = sum(
        1
        for key, group in alpha_groups.items()
        if len(group) > 1 and len(exact_keys_by_alpha[key]) > 1
    )

    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=False)
    source_counts = dict(sorted(Counter(str(row["paper_dataset"]) for row in rows).items()))
    summary = {
        "schema": "same-resource-atp-input-overlap-audit-v1",
        "input": {
            "records": len(rows),
            "unique_record_ids": len(set(ids)),
            "source_counts": source_counts,
        },
        "exact_directed_implication": {
            "unique_problems": len(exact_groups),
            "duplicate_groups": len(exact_duplicates),
            "records_in_duplicate_groups": sum(len(group) for group in exact_duplicates),
            "redundant_records": len(rows) - len(exact_groups),
            "cross_source_groups": len(exact_cross),
            "cross_source_group_counts": pair_counts(exact_cross),
        },
        "alpha_renaming_and_equation_symmetry": {
            "unique_problems": len(alpha_groups),
            "duplicate_groups": len(alpha_duplicates),
            "records_in_duplicate_groups": sum(len(group) for group in alpha_duplicates),
            "redundant_records": len(rows) - len(alpha_groups),
            "cross_source_groups": len(alpha_cross),
            "cross_source_group_counts": pair_counts(alpha_cross),
            "groups_not_already_exact_duplicates": alpha_only_group_count,
        },
        "interpretation": {
            "frozen_input_changed": False,
            "source_specific_denominators": source_counts,
            "overall_unique_denominator_exact": len(exact_groups),
            "overall_unique_denominator_alpha": len(alpha_groups),
        },
    }
    with (output_dir / "summary.json").open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")

    fields = (
        "equivalence",
        "group_id",
        "group_size",
        "sources",
        "record_id",
        "paper_dataset",
        "original_problem_id",
        "source_eq_id",
        "target_eq_id",
        "equation1",
        "equation2",
    )
    with (output_dir / "duplicate_members.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for equivalence, groups, key_name in (
            ("exact", exact_duplicates, "_exact_key"),
            ("alpha", alpha_duplicates, "_alpha_key"),
        ):
            for group in sorted(groups, key=lambda item: str(item[0][key_name])):
                group_id = f"{equivalence}_{sha256_text(str(group[0][key_name]))[:16]}"
                sources = "+".join(sorted({str(row["paper_dataset"]) for row in group}))
                for row in group:
                    writer.writerow(
                        {
                            "equivalence": equivalence,
                            "group_id": group_id,
                            "group_size": len(group),
                            "sources": sources,
                            "record_id": row["id"],
                            "paper_dataset": row["paper_dataset"],
                            "original_problem_id": row.get("original_problem_id", ""),
                            "source_eq_id": row.get("source_eq_id", row.get("eq1_id", "")),
                            "target_eq_id": row.get("target_eq_id", row.get("eq2_id", "")),
                            "equation1": row["equation1"],
                            "equation2": row["equation2"],
                        }
                    )

    priority = {source: index for index, source in enumerate(SOURCE_PRIORITY)}
    with (output_dir / "unique_representatives.jsonl").open(
        "w", encoding="utf-8", newline="\n"
    ) as handle:
        for alpha_key in sorted(alpha_groups):
            group = alpha_groups[alpha_key]
            representative = min(
                group,
                key=lambda row: (
                    priority.get(str(row["paper_dataset"]), len(priority)),
                    ids.index(str(row["id"])),
                ),
            )
            public = {key: value for key, value in representative.items() if not key.startswith("_")}
            public["equivalence_group_id"] = f"alpha_{sha256_text(alpha_key)[:16]}"
            public["provenance_sources"] = sorted(
                {str(row["paper_dataset"]) for row in group}
            )
            public["equivalent_record_ids"] = [str(row["id"]) for row in group]
            handle.write(canonical_json(public) + "\n")

    print(canonical_json(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
