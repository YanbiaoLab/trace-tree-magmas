#!/usr/bin/env python3
"""Audit Austin96 discoveries against the released ALPS result tables.

This is a data-only audit.  It does not invoke a solver or a judge.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    rows = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSON on line {line_number} of {path.name}") from exc
    return rows


def parse_term(text: str):
    """Parse the fully parenthesized magma syntax used by ETP and ALPS."""
    text = text.replace("◇", "*").replace("⋄", "*").replace("\u22c6", "*")
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_]*|[()*]", text)
    position = 0

    def primary():
        nonlocal position
        if position >= len(tokens):
            raise ValueError(f"unexpected end of term: {text!r}")
        token = tokens[position]
        if token == "(":
            position += 1
            node = product()
            if position >= len(tokens) or tokens[position] != ")":
                raise ValueError(f"unbalanced parentheses in term: {text!r}")
            position += 1
            return node
        if token in {"*", ")"}:
            raise ValueError(f"unexpected token {token!r} in term: {text!r}")
        position += 1
        return ("var", token)

    def product():
        nonlocal position
        node = primary()
        while position < len(tokens) and tokens[position] == "*":
            position += 1
            node = ("op", node, primary())
        return node

    result = product()
    if position != len(tokens):
        raise ValueError(f"unparsed tokens in term: {text!r}")
    return result


def normalize_law(text: str) -> str:
    """Canonicalize an equation modulo consistent variable renaming."""
    if "=" not in text:
        raise ValueError(f"law has no equality: {text!r}")
    left_text, right_text = text.split("=", 1)
    tree = ("eq", parse_term(left_text), parse_term(right_text))
    variable_map: dict[str, str] = {}

    def canonical(node):
        if node[0] == "var":
            name = node[1]
            if name not in variable_map:
                variable_map[name] = f"v{len(variable_map)}"
            return ("var", variable_map[name])
        return (node[0], *(canonical(child) for child in node[1:]))

    return repr(canonical(tree))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_csv(path: Path, rows: list[dict], columns: list[str]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=columns, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--austin96", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--alps-austin-laws", type=Path, required=True)
    parser.add_argument("--alps-final-status", type=Path, required=True)
    parser.add_argument("--alps-evaluation-pool", type=Path, required=True)
    parser.add_argument("--alps-baseline", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)
    austin96 = read_jsonl(args.austin96)
    experiment = read_jsonl(args.results)
    alps_screening = read_jsonl(args.alps_austin_laws)
    alps_final_status = read_jsonl(args.alps_final_status)
    alps_pool = read_jsonl(args.alps_evaluation_pool)
    alps_baseline = read_jsonl(args.alps_baseline)

    id_by_law: dict[str, int] = {}
    source_by_id: dict[int, dict] = {}
    for row in austin96:
        eq_id = int(row["source_eq_id"])
        law = row["source_equation"]
        key = normalize_law(law)
        if key in id_by_law and id_by_law[key] != eq_id:
            raise ValueError(f"normalized-law collision: E{id_by_law[key]} and E{eq_id}")
        id_by_law[key] = eq_id
        source_by_id[eq_id] = row

    if len(austin96) != 96 or len(id_by_law) != 96:
        raise ValueError(f"expected 96 distinct Austin96 laws, got {len(austin96)}/{len(id_by_law)}")

    known: dict[int, dict] = {}
    for row in alps_screening:
        eq_id = id_by_law.get(normalize_law(row["law"]))
        if eq_id is not None:
            known[eq_id] = {
                "alps_stage": "screening",
                "alps_config": "screening certificate",
                "alps_budget_s": "",
                "alps_verdict": "AUSTIN",
            }

    for row in alps_baseline:
        if row.get("verdict") != "AUSTIN":
            continue
        eq_id = id_by_law.get(normalize_law(row["law"]))
        if eq_id is not None:
            known[eq_id] = {
                "alps_stage": "residual portfolio",
                "alps_config": row.get("config", ""),
                "alps_budget_s": row.get("budget", ""),
                "alps_verdict": row["verdict"],
            }

    pool_by_id: dict[int, dict] = {}
    for row in alps_pool:
        eq_id = id_by_law.get(normalize_law(row["law"]))
        if eq_id is not None:
            pool_by_id[eq_id] = row

    final_status_by_id: dict[int, dict] = {}
    for row in alps_final_status:
        eq_id = id_by_law.get(normalize_law(row["law"]))
        if eq_id is not None:
            final_status_by_id[eq_id] = row

    accepted: dict[int, dict] = {}
    for row in experiment:
        legacy_accepted = (
            row.get("paper_dataset") == "austin96"
            and row.get("search_program") == "infinite_v13"
            and row.get("status") == "accepted"
            and row.get("verdict") == "false"
        )
        current_accepted = (
            row.get("paper_dataset") == "austin96"
            and row.get("judge_status") == "accepted"
            and row.get("family") in {"trace", "guarded", "completion", "cnf"}
        )
        if legacy_accepted or current_accepted:
            eq_id = int(row["eq1_id"])
            if eq_id in accepted:
                raise ValueError(f"duplicate selected accepted result for E{eq_id}")
            if current_accepted:
                source = source_by_id[eq_id]
                accepted[eq_id] = {
                    **row,
                    "paper_dataset_position": source["paper_dataset_position"],
                    "equation1": source["equation1"],
                    "status": "accepted",
                    "verdict": "false",
                    "search_metadata": {
                        "subprocedure": row["family"],
                        "orientation": "selected tuned profile",
                    },
                    "certificates": [{"sha256": row["certificate_sha256"]}],
                }
            else:
                accepted[eq_id] = row

    matrix = []
    for eq_id, row in sorted(accepted.items(), key=lambda item: item[1]["paper_dataset_position"]):
        metadata = row.get("search_metadata") or {}
        certs = row.get("certificates") or []
        prior = known.get(eq_id)
        pool = pool_by_id.get(eq_id)
        final_status = final_status_by_id.get(eq_id)
        matrix.append(
            {
                "equation_id": f"E{eq_id}",
                "dual_pair_index": (int(row["paper_dataset_position"]) + 1) // 2,
                "equation": row["equation1"],
                "our_status": row["status"],
                "our_verdict": row["verdict"],
                "subprocedure": metadata.get("subprocedure", ""),
                "orientation": metadata.get("orientation", ""),
                "certificate_sha256": certs[0]["sha256"] if certs else "",
                "known_in_alps_before_our_work": "yes" if prior else "no",
                "alps_stage": prior["alps_stage"] if prior else "",
                "alps_config": prior["alps_config"] if prior else "",
                "alps_screening_status": final_status.get("status", "") if final_status else "",
                "alps_pool_tier": pool.get("tier", "") if pool else "not-in-pool",
                "alps_pool_baseline_resolution": (
                    json.dumps(pool.get("baseline_resolution"), sort_keys=True)
                    if pool and pool.get("baseline_resolution") is not None
                    else "null"
                ),
                "novel_relative_to_alps": "no" if prior else "yes",
            }
        )

    known_rows = []
    for eq_id, prior in sorted(known.items()):
        known_rows.append(
            {
                "equation_id": f"E{eq_id}",
                "equation": source_by_id[eq_id]["source_equation"],
                **prior,
                "also_accepted_by_our_selected_searches": "yes" if eq_id in accepted else "no",
            }
        )

    accepted_ids = set(accepted)
    known_ids = set(known)
    overlap = accepted_ids & known_ids
    candidate_new = accepted_ids - known_ids
    pair_keys = {
        (int(accepted[eq_id]["paper_dataset_position"]) + 1) // 2 for eq_id in candidate_new
    }
    candidate_new_hard_null = {
        eq_id
        for eq_id in candidate_new
        if eq_id in pool_by_id
        and pool_by_id[eq_id].get("tier") == "hard"
        and pool_by_id[eq_id].get("baseline_resolution") is None
    }
    candidate_new_not_in_pool = candidate_new - candidate_new_hard_null
    pair_members: dict[int, list[int]] = {}
    for eq_id in candidate_new:
        pair_index = (int(accepted[eq_id]["paper_dataset_position"]) + 1) // 2
        pair_members.setdefault(pair_index, []).append(eq_id)
    if any(len(members) != 2 for members in pair_members.values()):
        raise ValueError(f"candidate-new duality grouping is incomplete: {pair_members}")
    pair_rows = []
    for pair_index, members in sorted(pair_members.items()):
        members.sort(key=lambda eq_id: accepted[eq_id]["paper_dataset_position"])
        pair_rows.append(
            {
                "dual_pair_index": pair_index,
                "equation_id_a": f"E{members[0]}",
                "equation_id_b": f"E{members[1]}",
                "alps_status_a": (
                    "hard/null" if members[0] in candidate_new_hard_null else "not-in-screened-corpus"
                ),
                "alps_status_b": (
                    "hard/null" if members[1] in candidate_new_hard_null else "not-in-screened-corpus"
                ),
            }
        )
    summary = {
        "schema": "austin96-novelty-audit-v2",
        "austin96_input_count": len(austin96),
        "austin96_present_in_alps_final_status_count": len(final_status_by_id),
        "austin96_present_in_alps_evaluation_pool_count": len(pool_by_id),
        "austin96_absent_from_alps_screened_corpus_ids": [
            f"E{x}" for x in sorted(set(source_by_id) - set(final_status_by_id))
        ],
        "our_accepted_law_count": len(accepted_ids),
        "alps_known_austin96_law_count": len(known_ids),
        "overlap_law_count": len(overlap),
        "overlap_equation_ids": [f"E{x}" for x in sorted(overlap)],
        "candidate_new_relative_to_alps_law_count": len(candidate_new),
        "candidate_new_relative_to_alps_dual_pair_count": len(pair_keys),
        "candidate_new_with_alps_hard_null_row_count": len(candidate_new_hard_null),
        "candidate_new_not_in_alps_evaluation_pool_count": len(candidate_new_not_in_pool),
        "candidate_new_not_in_alps_evaluation_pool_ids": [
            f"E{x}" for x in sorted(candidate_new_not_in_pool)
        ],
        "candidate_new_equation_ids": [f"E{x}" for x in sorted(candidate_new)],
        "claim_scope": "exact ETP equation IDs, relative to the pinned ALPS result tables",
    }

    write_csv(
        args.out / "novelty_matrix.csv",
        matrix,
        [
            "equation_id",
            "dual_pair_index",
            "equation",
            "our_status",
            "our_verdict",
            "subprocedure",
            "orientation",
            "certificate_sha256",
            "known_in_alps_before_our_work",
            "alps_stage",
            "alps_config",
            "alps_screening_status",
            "alps_pool_tier",
            "alps_pool_baseline_resolution",
            "novel_relative_to_alps",
        ],
    )
    write_csv(
        args.out / "alps_known_austin96.csv",
        known_rows,
        [
            "equation_id",
            "equation",
            "alps_stage",
            "alps_config",
            "alps_budget_s",
            "alps_verdict",
            "also_accepted_by_our_selected_searches",
        ],
    )
    write_csv(
        args.out / "candidate_new_dual_pairs.csv",
        pair_rows,
        [
            "dual_pair_index",
            "equation_id_a",
            "equation_id_b",
            "alps_status_a",
            "alps_status_b",
        ],
    )
    (args.out / "summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    source_hashes = {
        "schema": "novelty-audit-source-hashes-v1",
        "files": [
            {"role": "austin96", "name": args.austin96.name, "sha256": sha256(args.austin96)},
            {"role": "our_results", "name": args.results.name, "sha256": sha256(args.results)},
            {
                "role": "alps_screening",
                "name": args.alps_austin_laws.name,
                "sha256": sha256(args.alps_austin_laws),
            },
            {
                "role": "alps_final_status",
                "name": args.alps_final_status.name,
                "sha256": sha256(args.alps_final_status),
            },
            {
                "role": "alps_evaluation_pool",
                "name": args.alps_evaluation_pool.name,
                "sha256": sha256(args.alps_evaluation_pool),
            },
            {
                "role": "alps_residual_portfolio",
                "name": args.alps_baseline.name,
                "sha256": sha256(args.alps_baseline),
            },
        ],
    }
    (args.out / "source_hashes.json").write_text(
        json.dumps(source_hashes, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
