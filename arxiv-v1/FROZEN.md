# Frozen arXiv v1 snapshot

This directory is an immutable snapshot prepared on 2026-09-05 for arXiv
version 1. It contains the manuscript, source code, frozen inputs, recorded
results, Lean certificates, Judge receipts, and the scripts needed to verify
the public artifact.

Do not modify files in this directory in place after publication. Corrections,
new experiments, or revised manuscripts should be placed in a new versioned
directory. File integrity is recorded in `SHA256SUMS`; from this directory, run
`python -B verify_all.py` to perform the complete offline verification.
