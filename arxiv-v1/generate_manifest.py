#!/usr/bin/env python3
"""Regenerate the deterministic repository-wide SHA-256 inventory."""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "SHA256SUMS"


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def main() -> int:
    files = [
        path
        for path in ROOT.rglob("*")
        if path.is_file()
        and path != OUTPUT
        and ".git" not in path.relative_to(ROOT).parts
        and "__pycache__" not in path.relative_to(ROOT).parts
        and path.suffix != ".pyc"
    ]
    lines = [
        f"{digest(path)}  {path.relative_to(ROOT).as_posix()}"
        for path in sorted(files)
    ]
    OUTPUT.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote SHA256SUMS: {len(lines)} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
