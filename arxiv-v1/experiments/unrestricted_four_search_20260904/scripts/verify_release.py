#!/usr/bin/env python3
"""Verify completeness, hashes, counting semantics, and privacy boundary."""

from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
FAMILIES = ("trace", "guarded", "completion", "cnf")


def read_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def read_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def canonical_problem(row: dict) -> bytes:
    payload = {
        "id": row["id"],
        "eq1_id": row["eq1_id"],
        "eq2_id": row["eq2_id"],
        "equation1": row["equation1"],
        "equation2": row["equation2"],
    }
    return json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("ascii")


def independently_recompute_test_sets(
    input_rows: list[dict], family_sets: dict[str, set[str]]
) -> dict:
    union = set().union(*family_sets.values())

    def members(row: dict, prefixes: tuple[str, ...]) -> list[str]:
        values = set(str(value) for value in row.get("equivalent_record_ids", []))
        values.add(str(row["id"]))
        return sorted(
            value for value in values if any(value.startswith(prefix) for prefix in prefixes)
        )

    def view(name: str, prefixes: tuple[str, ...]) -> dict:
        groups = {
            str(row["id"]): members(row, prefixes)
            for row in input_rows
            if members(row, prefixes)
        }
        originals = {value for values in groups.values() for value in values}

        def coverage(problem_ids: set[str]) -> dict:
            hit_groups = set(groups) & problem_ids
            covered = {value for group in hit_groups for value in groups[group]}
            native = {
                group
                for group in hit_groups
                if any(group.startswith(prefix) for prefix in prefixes)
            }
            return {
                "accepted_equivalence_classes": len(hit_groups),
                "covered_original_records_via_equivalence": len(covered),
                "accepted_representatives_with_source_native_id": len(native),
            }

        return {
            "name": name,
            "original_records": len(originals),
            "alpha_symmetry_equivalence_classes": len(groups),
            "collapsed_redundant_records": len(originals) - len(groups),
            "families": {
                family: coverage(family_sets[family]) for family in FAMILIES
            },
            "four_family_union": coverage(union),
        }

    order5 = view("order5", ("austin96::", "generality34::"))
    alps = view("alps4141", ("alps4141::",))
    cross = sum(
        bool(members(row, ("alps4141::",)))
        and bool(members(row, ("austin96::", "generality34::")))
        for row in input_rows
    )
    assert order5["original_records"] == 130
    assert order5["alpha_symmetry_equivalence_classes"] == 130
    assert alps["original_records"] == 4141
    assert alps["alpha_symmetry_equivalence_classes"] == 4140
    assert cross == 83
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
        "cross_source_equivalence_classes": cross,
        "combined_execution_representatives": len(input_rows),
    }


def assert_no_forbidden_result_keys(value: object, path: str = "$") -> None:
    forbidden = {
        "sandbox_id",
        "run_id",
        "control_job_id",
        "control_backend_url",
        "submitted_at",
        "code",
        "stdout",
        "stderr",
    }
    if isinstance(value, dict):
        overlap = forbidden & set(value)
        assert not overlap, f"forbidden result keys at {path}: {sorted(overlap)}"
        for key, child in value.items():
            assert_no_forbidden_result_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            assert_no_forbidden_result_keys(child, f"{path}[{index}]")


def main() -> int:
    summary = read_json(RESULTS / "summary.json")
    rows = read_jsonl(RESULTS / "per_profile_results.jsonl")
    receipts = read_jsonl(RESULTS / "judge_receipts.jsonl")
    fluctuation = read_jsonl(RESULTS / "trace_fluctuation_supplement.jsonl")
    accepted = read_json(RESULTS / "accepted_sets.json")
    judge_contract = read_json(ROOT / "config" / "judge_contract.json")
    input_rows = read_jsonl(ROOT / "inputs" / "all_4187.jsonl")
    input_by_id = {row["id"]: row for row in input_rows}
    assert len(input_by_id) == len(input_rows) == 4187
    problem_hashes = {
        problem_id: hashlib.sha256(canonical_problem(row)).hexdigest()
        for problem_id, row in input_by_id.items()
    }

    assert len(rows) == 4271, len(rows)
    expected_profile_records = {
        "trace_depth_sweep_soundfix_v5": 4187,
        "guarded_contract_first_v1": 2,
        "completion_hybrid_soundfix_v5": 61,
        "completion_generalized_index0_full_v1": 1,
        "completion_indexed_all_v1": 3,
        "cnf_nf16_reverse_ties_completed_first_sound_v3": 17,
    }
    assert Counter(row["profile"] for row in rows) == expected_profile_records
    assert Counter(row["judge_status"] for row in rows)["lean_timeout_60m_client_cutoff"] == 3
    assert not any(
        row["judge_status"] in {"incorrect", "rejected", "malformed"} for row in rows
    )
    assert len(receipts) == 731
    assert Counter(row["status"] for row in receipts) == {
        "accepted": 728,
        "lean_timeout_60m_client_cutoff": 3,
    }
    assert len(fluctuation) == 12
    assert all(not row["counted_in_fresh_round115"] for row in fluctuation)
    for row in rows:
        problem = input_by_id[row["problem_id"]]
        assert row["eq1_id"] == problem["eq1_id"]
        assert row["eq2_id"] == problem["eq2_id"]
        assert row["problem_sha256"] == problem_hashes[row["problem_id"]]

    family_sets = {name: set(ids) for name, ids in accepted["families"].items()}
    assert {name: len(ids) for name, ids in family_sets.items()} == {
        "trace": 636,
        "guarded": 2,
        "completion": 61,
        "cnf": 17,
    }
    union = set().union(*family_sets.values())
    assert len(union) == 668
    assert set(accepted["union"]) == union
    fluctuation_ids = set(accepted["trace_fluctuation_supplement_not_in_primary_union"])
    assert len(fluctuation_ids) == 12
    assert len(fluctuation_ids - union) == 10
    assert len(union | fluctuation_ids) == 678
    assert summary["four_family_union"]["accepted_unique_problems"] == 668
    assert summary["four_family_union"]["order5"] == 44
    assert "generalization" not in summary["benchmark"]
    assert "generalization" not in summary["four_family_union"]
    assert summary["cleanliness"]["non_timeout_lean_rejected"] == 0

    recomputed_family_sets = {
        family: {
            row["problem_id"]
            for row in rows
            if row["family"] == family and row["judge_status"] == "accepted"
        }
        for family in ("trace", "guarded", "completion", "cnf")
    }
    assert recomputed_family_sets == family_sets
    test_sets = independently_recompute_test_sets(input_rows, family_sets)
    assert read_json(RESULTS / "test_set_breakdown.json") == test_sets
    assert summary["test_set_reporting"] == {
        "breakdown_path": "results/test_set_breakdown.json",
        "order5_union_equivalence_classes": test_sets["order5"]["four_family_union"]["accepted_equivalence_classes"],
        "alps4141_union_equivalence_classes": test_sets["alps4141"]["four_family_union"]["accepted_equivalence_classes"],
        "alps4141_union_original_records_via_equivalence": test_sets["alps4141"]["four_family_union"]["covered_original_records_via_equivalence"],
        "combined_668_is_overlap_audit_only": True,
    }

    receipt_by_key = {
        (row["profile"], row["problem_id"], row["certificate_sha256"]): row
        for row in receipts
    }
    assert len(receipt_by_key) == len(receipts)
    receipt_keys = set(receipt_by_key)
    certificate_paths = set()
    for row in rows:
        if row["generation_status"] != "generated":
            assert row["certificate_path"] is None
            continue
        key = (row["profile"], row["problem_id"], row["certificate_sha256"])
        assert key in receipt_keys, key
        receipt = receipt_by_key[key]
        for field in (
            "profile",
            "family",
            "problem_id",
            "eq1_id",
            "eq2_id",
            "certificate_path",
            "certificate_sha256",
            "certificate_bytes",
            "problem_sha256",
        ):
            assert receipt[field] == row[field], (key, field)
        assert receipt["verdict"] == judge_contract["accepted_verdict"]
        if receipt["status"] == "accepted":
            assert receipt["judge_response_received"] is True
            assert receipt["service_revision"] == judge_contract["service_revision"]
            assert receipt["proof_policy_revision"] == judge_contract["proof_policy_revision"]
            assert len(receipt["axioms"]) == len(set(receipt["axioms"]))
            assert set(receipt["axioms"]) <= set(judge_contract["allowed_axioms"])
        else:
            assert receipt["status"] == "lean_timeout_60m_client_cutoff"
            assert receipt["judge_response_received"] is False
            assert receipt["timeout_origin"] == "experiment_policy_client_cutoff"
            assert receipt["timeout_seconds"] == 3600
        path = ROOT / row["certificate_path"]
        assert path.is_file(), path
        assert path.stat().st_size == row["certificate_bytes"]
        assert digest(path) == row["certificate_sha256"]
        assert row["certificate_bytes"] <= judge_contract["certificate_limit_bytes"]
        certificate_paths.add(path.resolve())
    for row in fluctuation:
        key = (row["profile"], row["problem_id"], row["certificate_sha256"])
        assert key in receipt_keys, key
        receipt = receipt_by_key[key]
        assert row["problem_sha256"] == problem_hashes[row["problem_id"]]
        assert receipt["problem_sha256"] == row["problem_sha256"]
        path = ROOT / row["certificate_path"]
        assert path.is_file(), path
        assert digest(path) == row["certificate_sha256"]
        certificate_paths.add(path.resolve())
    on_disk = {path.resolve() for path in (RESULTS / "certificates").rglob("*.lean")}
    assert certificate_paths == on_disk
    assert len(on_disk) == 731

    profiles = {}
    for profile in sorted({row["profile"] for row in rows}):
        selected = [row for row in rows if row["profile"] == profile]
        profiles[profile] = {
            "records": len(selected),
            "generation": dict(sorted(Counter(row["generation_status"] for row in selected).items())),
            "judge": dict(sorted(Counter(row["judge_status"] for row in selected).items())),
            "generated_unique_problems": len({row["problem_id"] for row in selected if row["generation_status"] == "generated"}),
            "accepted_unique_problems": len({row["problem_id"] for row in selected if row["judge_status"] == "accepted"}),
        }
    recomputed_summary = {
        "schema": "unrestricted-four-search-recomputed-summary-v1",
        "public_profile_rows": len(rows),
        "profiles": profiles,
        "selected_family_counts": {name: len(values) for name, values in family_sets.items()},
        "four_family_union": len(union),
        "trace_fluctuation_certificates": len(fluctuation_ids),
        "trace_fluctuation_incremental_over_primary_union": len(fluctuation_ids - union),
        "four_family_union_plus_trace_fluctuation": len(union | fluctuation_ids),
        "test_sets": test_sets,
    }
    assert read_json(RESULTS / "recomputed_summary.json") == recomputed_summary

    input_manifest = read_json(ROOT / "inputs" / "manifest.json")
    for name, record in input_manifest["files"].items():
        path = ROOT / "inputs" / name
        assert path.is_file()
        assert digest(path) == record["sha256"]
        assert sum(1 for line in path.open("r", encoding="utf-8") if line.strip()) == record["records"]
    variant_manifest = read_json(ROOT / "config" / "variant_manifest.json")
    for record in variant_manifest["profiles"].values():
        assert digest(ROOT / record["path"]) == record["sha256"]

    for value in (rows, receipts, fluctuation, accepted, summary):
        assert_no_forbidden_result_keys(value)

    privacy_patterns = {
        "windows_absolute_path": re.compile(r"[A-Za-z]:\\\\(?:Users|Desktop)\\\\", re.I),
        "private_ipv4_url": re.compile(r"https?://(?:10|127|192\\.168)\\.", re.I),
        "sandbox_instance_id": re.compile(r"default--[a-z0-9-]{8,}", re.I),
        "credential_assignment": re.compile(
            r"(?im)^(?:E2B_API_KEY|JUDGE_API_KEY)=(?!<)[^\\s]+$"
        ),
    }
    privacy_hits = []
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.name == "SHA256SUMS" or path.suffix == ".pyc":
            continue
        if path.suffix.lower() not in {".md", ".json", ".jsonl", ".csv", ".py", ".toml", ".lock", ".example"}:
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        for name, pattern in privacy_patterns.items():
            if pattern.search(text):
                privacy_hits.append((path.relative_to(ROOT).as_posix(), name))
    assert not privacy_hits, privacy_hits

    manifest_lines = (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    manifest = {}
    for line in manifest_lines:
        expected_hash, relative = line.split("  ", 1)
        assert relative not in manifest
        manifest[relative] = expected_hash
    current_files = {
        path.relative_to(ROOT).as_posix()
        for path in ROOT.rglob("*")
        if path.is_file()
        and path.name != "SHA256SUMS"
        and "__pycache__" not in path.parts
        and path.suffix != ".pyc"
    }
    assert set(manifest) == current_files
    for relative, expected_hash in manifest.items():
        assert digest(ROOT / relative) == expected_hash, relative

    print(
        json.dumps(
            {
                "status": "verified",
                "public_result_rows": len(rows),
                "certificates": len(on_disk),
                "judge_receipts": len(receipts),
                "accepted_receipts": 728,
                "client_policy_timeouts": 3,
                "four_family_union": len(union),
                "privacy_hits": 0,
                "manifest_entries": len(manifest),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
