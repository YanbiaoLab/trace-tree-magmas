# Reproducibility

## Offline verification

Python 3.11 or newer is sufficient for the read-only verifiers; they use only
the standard library.

```text
python scripts/verify_results.py --experiment-root .
python scripts/verify_public_artifact.py --root . --check
```

`verify_results.py` checks all 12,813 sanitized per-problem rows, input order
and hashes, source splits, exact/alpha deduplications, primary benchmark
counts, manifest entries, and every retained evidence stream. It decompresses
the original stdout/stderr payloads and independently reconstructs the SZS and
proof-block classifications without importing the remote worker.

## Full remote rerun

The full campaign requires the separately distributed sandbox runtime and the
three pinned Linux binaries whose SHA-256 hashes are in
`config/tool_sources.json`. For each tool, invoke:

```text
python scripts/run_remote_atp.py \
  --tool TOOL \
  --binary PATH_TO_PINNED_BINARY \
  --worker scripts/remote_worker.py \
  --input inputs/combined_4271.jsonl \
  --output PRIVATE_RAW_ROOT/TOOL/raw_results.jsonl \
  --private-lifecycle PRIVATE_OUTSIDE_RELEASE/TOOL/lifecycle.jsonl \
  --summary PRIVATE_OUTSIDE_RELEASE/TOOL/summary.json \
  --runtime-root PATH_TO_SOLVER_RUNTIME_SANDBOX \
  --concurrency 150
```

Valid `TOOL` values are `vampire`, `eprover`, and `twee_complete`. The runner
hash-checks each uploaded binary and performs a remote self-check before
scheduling problems. It never invokes an ATP binary locally. Resume the same
command after interruption; unique record IDs prevent duplicate final rows.

If terminal infrastructure errors remain, use `prepare_retry_input.py`, rerun
only those exact IDs, and combine them with `merge_retry_results.py`. Then run
`independent_reparse.py` on every final raw file and build the public package
with `postprocess_results.py`.

## Determinism boundary

Inputs, commands, solver binaries, classification logic, and aggregate
calculations are frozen. Exact wall times and sampled RSS can vary with remote
host scheduling. Such variation may change near-boundary successes, so a rerun
must report its own per-problem results rather than silently replacing the
released measurements.

Judge v3 is not applicable to ATP text. `judge_canary/` records a separate
accepted canary establishing the service/proof-policy revision used elsewhere
in the repository.

