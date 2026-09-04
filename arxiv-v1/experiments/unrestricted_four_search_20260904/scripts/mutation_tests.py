#!/usr/bin/env python3
"""Prove that release verification rejects six evidence mutations."""

from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


SOURCE = Path(__file__).resolve().parents[1]


def run(root: Path, script: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-B", str(root / "scripts" / script)],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n" for row in rows),
        encoding="utf-8",
        newline="\n",
    )


def refresh(root: Path) -> None:
    result = run(root, "generate_manifest.py")
    if result.returncode:
        raise RuntimeError(result.stdout)


def expect_rejected(root: Path, label: str) -> None:
    refresh(root)
    result = run(root, "verify_release.py")
    if result.returncode == 0:
        raise AssertionError(f"mutation was accepted: {label}")


def restore(root: Path, relative: str) -> None:
    shutil.copy2(SOURCE / relative, root / relative)


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="four-search-mutations-") as temporary:
        root = Path(temporary) / "artifact"
        shutil.copytree(SOURCE, root)
        baseline = run(root, "verify_release.py")
        if baseline.returncode:
            raise RuntimeError(baseline.stdout)

        receipt_path = root / "results" / "judge_receipts.jsonl"
        receipts = jsonl(receipt_path)
        receipts[0]["problem_id"], receipts[1]["problem_id"] = receipts[1]["problem_id"], receipts[0]["problem_id"]
        write_jsonl(receipt_path, receipts)
        expect_rejected(root, "swapped receipt problem IDs")
        restore(root, "results/judge_receipts.jsonl")

        receipts = jsonl(receipt_path)
        accepted = next(row for row in receipts if row["status"] == "accepted")
        accepted["service_revision"] += "-mutated"
        write_jsonl(receipt_path, receipts)
        expect_rejected(root, "Judge service revision")
        restore(root, "results/judge_receipts.jsonl")

        receipts = jsonl(receipt_path)
        receipts[0]["certificate_sha256"] = "0" * 64
        write_jsonl(receipt_path, receipts)
        expect_rejected(root, "receipt certificate hash")
        restore(root, "results/judge_receipts.jsonl")

        result_path = root / "results" / "per_profile_results.jsonl"
        result_rows = jsonl(result_path)
        result_rows[0]["problem_id"] = result_rows[1]["problem_id"]
        write_jsonl(result_path, result_rows)
        expect_rejected(root, "result problem ID")
        restore(root, "results/per_profile_results.jsonl")

        summary_path = root / "results" / "summary.json"
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
        summary["four_family_union"]["accepted_unique_problems"] += 1
        summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
        expect_rejected(root, "aggregate summary")
        restore(root, "results/summary.json")

        receipt = jsonl(receipt_path)[0]
        certificate = root / receipt["certificate_path"]
        raw = bytearray(certificate.read_bytes())
        raw[-1] ^= 1
        certificate.write_bytes(raw)
        expect_rejected(root, "certificate bytes")

    print(json.dumps({"baseline": "accepted", "mutations_rejected": 6}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
