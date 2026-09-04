#!/usr/bin/env python3
"""Offline verification for the tuned Austin96 novelty audit."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def verify_manifest() -> None:
    expected = {}
    for line in (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        digest, relative = line.split("  ", 1)
        if relative in expected:
            raise ValueError("duplicate manifest path")
        expected[relative] = digest
    actual = {
        path.relative_to(ROOT).as_posix()
        for path in ROOT.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS" and "__pycache__" not in path.parts
    }
    if set(expected) != actual:
        raise ValueError("manifest inventory mismatch")
    for relative, digest in expected.items():
        if sha256(ROOT / relative) != digest:
            raise ValueError(f"manifest hash mismatch: {relative}")


def main() -> int:
    verify_manifest()
    summary = json.loads((ROOT / "results" / "summary.json").read_text(encoding="utf-8"))
    required = {
        "our_accepted_law_count": 32,
        "alps_known_austin96_law_count": 6,
        "overlap_law_count": 4,
        "candidate_new_relative_to_alps_law_count": 28,
        "candidate_new_relative_to_alps_dual_pair_count": 14,
        "candidate_new_with_alps_hard_null_row_count": 24,
        "candidate_new_not_in_alps_evaluation_pool_count": 4,
    }
    for key, value in required.items():
        if summary[key] != value:
            raise ValueError(f"summary mismatch: {key}")
    if set(summary["overlap_equation_ids"]) != {"E19966", "E26105", "E22619", "E22634"}:
        raise ValueError("ALPS overlap ID mismatch")
    if not {"E9680", "E36524"} <= set(summary["candidate_new_equation_ids"]):
        raise ValueError("new tuned pair missing")

    with tempfile.TemporaryDirectory(prefix="novelty-audit-") as temporary:
        out = Path(temporary) / "results"
        command = [
            sys.executable,
            "-B",
            str(ROOT / "scripts" / "audit_novelty.py"),
            "--austin96", str(ROOT / "inputs" / "austin96.jsonl"),
            "--results", str(REPO / "experiments" / "unrestricted_four_search_20260904" / "results" / "per_profile_results.jsonl"),
            "--alps-austin-laws", str(ROOT / "inputs" / "alps" / "corpus" / "austin_laws.jsonl"),
            "--alps-final-status", str(ROOT / "inputs" / "alps" / "corpus" / "final_status.jsonl"),
            "--alps-evaluation-pool", str(ROOT / "inputs" / "alps" / "corpus" / "evaluation_pool.jsonl"),
            "--alps-baseline", str(ROOT / "inputs" / "alps" / "baseline" / "baseline_full_final.jsonl"),
            "--out", str(out),
        ]
        run = subprocess.run(command, cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
        if run.returncode:
            raise RuntimeError(run.stdout)
        frozen_files = {path.name for path in (ROOT / "results").iterdir() if path.is_file()}
        recomputed_files = {path.name for path in out.iterdir() if path.is_file()}
        if frozen_files != recomputed_files:
            raise ValueError("recomputed result inventory mismatch")
        for name in frozen_files:
            if (ROOT / "results" / name).read_bytes() != (out / name).read_bytes():
                raise ValueError(f"recomputed result differs: {name}")

    patterns = (
        re.compile(r"[A-Za-z]:\\(?:Users|Desktop)\\", re.I),
        re.compile(r"(?im)^(?:E2B_API_KEY|JUDGE_API_KEY)=(?!<)[^\s]+$"),
        re.compile(r"default--[a-z0-9-]{8,}", re.I),
    )
    for path in ROOT.rglob("*"):
        if path.is_file() and path.suffix.lower() in {".md", ".json", ".jsonl", ".csv", ".py"}:
            text = path.read_text(encoding="utf-8", errors="ignore")
            if any(pattern.search(text) for pattern in patterns):
                raise ValueError(f"privacy pattern: {path.relative_to(ROOT)}")

    print(json.dumps({"status": "verified", **required}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
