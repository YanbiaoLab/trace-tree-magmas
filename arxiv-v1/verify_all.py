"""One-command offline verifier for the Trace-Tree Magmas release."""

from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPERIMENTS = ROOT / "experiments"
FOUR_SEARCH = EXPERIMENTS / "unrestricted_four_search_20260904"
NOVELTY = EXPERIMENTS / "novelty_audit_austin96_20260904"
ATP = EXPERIMENTS / "same_resource_atp_baselines_20260904"
PAPER_PDF_SHA256 = "39551e4237a6add4e5393794148252900ba632d932cf053d5995eff8bf5619a0"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def verify_root_manifest() -> None:
    manifest = ROOT / "SHA256SUMS"
    if not manifest.is_file():
        raise SystemExit("missing repository SHA256SUMS")
    expected_paths: set[str] = set()
    for line_number, line in enumerate(
        manifest.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line.strip():
            continue
        try:
            expected, relative = line.split("  ", 1)
        except ValueError as exc:
            raise SystemExit(f"invalid SHA256SUMS line {line_number}") from exc
        expected_paths.add(relative)
        path = ROOT / Path(relative)
        if not path.is_file():
            raise SystemExit(f"manifest file is missing: {relative}")
        if sha256(path) != expected:
            raise SystemExit(f"manifest mismatch: {relative}")

    actual_paths = {
        path.relative_to(ROOT).as_posix()
        for path in ROOT.rglob("*")
        if path.is_file()
        and path != manifest
        and ".git" not in path.relative_to(ROOT).parts
        and "__pycache__" not in path.relative_to(ROOT).parts
    }
    if actual_paths != expected_paths:
        raise SystemExit(
            "repository manifest inventory differs; "
            f"unlisted={sorted(actual_paths - expected_paths)}, "
            f"absent={sorted(expected_paths - actual_paths)}"
        )


def run(arguments: list[str], cwd: Path) -> None:
    result = subprocess.run(
        [sys.executable, "-B", *arguments], cwd=cwd, check=False
    )
    if result.returncode:
        raise SystemExit(result.returncode)


def verify_paper_snapshot() -> None:
    pdf = ROOT / "paper" / "trace_tree_magmas.pdf"
    tex = ROOT / "paper" / "trace_tree_magmas.tex"
    if sha256(pdf) != PAPER_PDF_SHA256:
        raise SystemExit("paper PDF is not the supplied v16 snapshot")
    source = tex.read_text(encoding="utf-8")
    if "28 New Order-Five Austin" not in source:
        raise SystemExit("paper source is not the 28-new-identity version")


def main() -> None:
    verify_root_manifest()
    verify_paper_snapshot()
    run(["scripts/verify_release.py"], FOUR_SEARCH)
    run(["scripts/verify_release.py"], NOVELTY)
    run(["scripts/verify_results.py", "--experiment-root", "."], ATP)
    run(
        ["scripts/verify_public_artifact.py", "--root", ".", "--check"],
        ATP,
    )
    print("trace-tree-magmas release verification: PASS")


if __name__ == "__main__":
    main()
