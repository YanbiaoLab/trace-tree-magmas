# Reproducing the novelty matrix

This audit runs locally because it only reads and compares released JSONL
tables.  It performs no theorem proving, model search, or Judge call.  All
solver experiments remain remote-sandbox-only.

The exact ALPS files used by the audit are vendored under `inputs/alps/`, so
the result can be reproduced offline.  They are copied from ALPS commit
`e831af76da026edfa1697c970aeebb8098507b6d`; `inputs/alps/LICENSE` preserves
the upstream MIT license.  From the repository root, run:

```text
python experiments/novelty_audit_austin96_20260904/scripts/audit_novelty.py \
  --austin96 experiments/novelty_audit_austin96_20260904/inputs/austin96.jsonl \
  --results experiments/unrestricted_four_search_20260904/results/per_profile_results.jsonl \
  --alps-austin-laws experiments/novelty_audit_austin96_20260904/inputs/alps/austin_laws.jsonl \
  --alps-final-status experiments/novelty_audit_austin96_20260904/inputs/alps/final_status.jsonl \
  --alps-evaluation-pool experiments/novelty_audit_austin96_20260904/inputs/alps/evaluation_pool.jsonl \
  --alps-baseline experiments/novelty_audit_austin96_20260904/inputs/alps/baseline_full_final.jsonl \
  --out experiments/novelty_audit_austin96_20260904/results
```

Expected headline fields in `results/summary.json`:

```text
our_accepted_law_count = 32
alps_known_austin96_law_count = 6
overlap_law_count = 4
candidate_new_relative_to_alps_law_count = 28
candidate_new_relative_to_alps_dual_pair_count = 14
candidate_new_with_alps_hard_null_row_count = 24
candidate_new_not_in_alps_evaluation_pool_count = 4
```

The script fails on duplicate accepted rows, Austin96 size changes, normalized
law collisions, or incomplete dual-pair grouping.
