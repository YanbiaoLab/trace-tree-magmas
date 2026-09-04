# Reproducibility

## Requirements

- Python 3.12 and `uv`;
- access to a compatible remote Agent Sandbox provider;
- access to remote Judge v3;
- credentials supplied only through an untracked `.env` file.

Do not place the private run directory inside this artifact.  Raw generation
and Judge files include provider identifiers and are not publication-safe.

## Environment

```bash
uv sync --project runner/vendor --locked
cp runner/.env.example .env
# Replace placeholders locally; never commit .env.
```

The six executable profiles already encode a 120-second internal budget and a
1,024,000-byte certificate limit.  The controller enforces a 125-second outer
allowance and 2,000 MiB process-tree ceiling.

## Generation

Run every final profile remotely:

```bash
uv run --project runner/vendor python runner/run_campaign.py \
  --private-run-root ../private-unrestricted-reproduction \
  --runner-root runner/vendor \
  --concurrency 120
```

This performs the full 4,187 trace run and the exact supplemental regressions.
To rerun one profile, pass `--profile PROFILE`.  The target directory must not
already exist, preventing accidental overwrite.

## Candidate extraction and Judge

For each generated file, create a private candidate JSONL.  Example for trace:

```bash
python scripts/prepare_candidates.py \
  --results ../private-unrestricted-reproduction/trace_depth_sweep_soundfix_v5.generated.jsonl \
  --problems inputs/all_4187.jsonl \
  --family trace \
  --profile trace_depth_sweep_soundfix_v5 \
  --output ../private-unrestricted-reproduction/trace.candidates.jsonl
```

Submit every generated certificate, including overlaps:

```bash
PYTHONPATH=runner/vendor python scripts/submit_judge_v3.py \
  --candidates ../private-unrestricted-reproduction/trace.candidates.jsonl \
  --problems inputs/all_4187.jsonl \
  --output ../private-unrestricted-reproduction/trace.judge.jsonl \
  --concurrency 35
```

For `completion_hybrid_soundfix_v5`, add
`--request-timeout-seconds 3600`.  A client timeout means only that no terminal
response arrived within the experiment policy; it is not a Judge rejection.
Run `completion_indexed_all_v1` on
`inputs/final_supplemental_completion_indexed3.jsonl` to reproduce the accepted
replacement certificates.  Run `completion_generalized_index0_full_v1` on
`inputs/completion_E9001325.jsonl` for the one-problem supplement.

Judge caches may make a repeated submission much faster than the first
submission.  Status and certificate hash, rather than cached wall time, are the
reproducibility invariant.

## Public artifact verification

```bash
python scripts/recompute_summary.py
python scripts/generate_manifest.py
python scripts/verify_release.py
```

The verifier checks row cardinalities, family/problem counting, every Lean-file
hash and size, Judge receipt coverage, input and executable hashes, the
SHA-256 manifest, forbidden result fields, and privacy patterns.
