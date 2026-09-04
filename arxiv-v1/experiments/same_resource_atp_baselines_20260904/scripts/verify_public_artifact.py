#!/usr/bin/env python3
"""Build or verify the hash/privacy manifest for this public experiment."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
from pathlib import Path
from typing import Any


MANIFEST_NAME = "PUBLIC_MANIFEST.json"
PRIVATE_PATTERNS = {
    "control_plane_name": re.compile(rb"default--math-distill", re.IGNORECASE),
    "sandbox_identifier": re.compile(
        rb"[\"']sandbox_id[\"']\s*:\s*[\"'][A-Za-z0-9_-]{8,}[\"']",
        re.IGNORECASE,
    ),
    "secret_token": re.compile(rb"(?:^|[^A-Za-z0-9])sk-[A-Za-z0-9_-]{8,}"),
    "embedded_credential": re.compile(
        rb"(?:api[_-]?key|token|secret)[\"']?\s*[:=]\s*[\"'][^\"']{8,}[\"']",
        re.IGNORECASE,
    ),
    "local_windows_path": re.compile(
        rb"[A-Za-z]:\\(?:Users|Desktop)\\", re.IGNORECASE
    ),
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    return parser.parse_args()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def public_files(root: Path) -> list[Path]:
    return sorted(
        path
        for path in root.rglob("*")
        if path.is_file()
        and path.name != MANIFEST_NAME
        and "__pycache__" not in path.parts
        and path.suffix != ".pyc"
    )


def privacy_hits(path: Path) -> list[str]:
    if path.suffix == ".gz":
        with gzip.open(path, "rb") as handle:
            payload = handle.read()
    else:
        payload = path.read_bytes()
    hits = [name for name, pattern in PRIVATE_PATTERNS.items() if pattern.search(payload)]
    if path.name in {"postprocess_results.py", "verify_public_artifact.py"}:
        hits = [name for name in hits if name != "control_plane_name"]
    return hits


def build(root: Path) -> dict[str, Any]:
    files = []
    all_hits: list[dict[str, Any]] = []
    for path in public_files(root):
        relative = path.relative_to(root).as_posix()
        hits = privacy_hits(path)
        if hits:
            all_hits.append({"path": relative, "patterns": hits})
        files.append(
            {"path": relative, "bytes": path.stat().st_size, "sha256": sha256(path)}
        )
    if all_hits:
        raise ValueError(f"private-information patterns found: {all_hits}")
    return {
        "schema": "same-resource-atp-public-manifest-v1",
        "file_count": len(files),
        "privacy_pattern_hits": 0,
        "files": files,
    }


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    manifest_path = root / MANIFEST_NAME
    current = build(root)
    if args.write:
        with manifest_path.open("w", encoding="utf-8", newline="\n") as handle:
            json.dump(current, handle, indent=2, sort_keys=True, ensure_ascii=False)
            handle.write("\n")
        print(json.dumps({"manifest": MANIFEST_NAME, "files": current["file_count"]}))
        return 0

    expected = json.loads(manifest_path.read_text(encoding="utf-8"))
    if expected != current:
        raise ValueError("public manifest does not match the current artifact")
    print(
        json.dumps(
            {
                "manifest": MANIFEST_NAME,
                "files": current["file_count"],
                "privacy_pattern_hits": 0,
                "verified": True,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
