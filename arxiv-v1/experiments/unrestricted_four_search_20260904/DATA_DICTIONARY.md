# Data dictionary

## `results/per_profile_results.jsonl`

One row per executed profile/problem pair; 4,271 rows in total.

- `problem_id`, `eq1_id`, `eq2_id`: frozen benchmark identity;
- `dataset_partition`: `order5_130` or `generalization_4057`;
- `family`, `profile`, `profile_role`: method and exact executable role;
- `generation_status`: `generated`, `no_candidate`, or `memory_limit`;
- `solver_elapsed_seconds`: remote solver wall time recorded by the controller;
- `process_tree_peak_rss_bytes`, `memory_limit_bytes`: sampled peak and limit;
- `judge_status`: `accepted`, `lean_timeout_60m_client_cutoff`, or
  `not_submitted_no_certificate`;
- `certificate_*`: relative Lean path, UTF-8 byte count, and SHA-256, or null
  when no certificate was generated.

`no_candidate` includes ordinary completed search without a model.  It is not a
proof that no countermodel exists.  A sampled `memory_limit` row is resource
censored and likewise not a theorem.

## `results/judge_receipts.jsonl`

One privacy-sanitized row per submitted profile/certificate occurrence, plus an
explicit policy record for each of the three client cutoffs.  The public
allowlist retains identity, status, time, certificate hash/size/path, cache bit,
axiom list, and Judge revisions.  It omits source code (stored as `.lean`), raw
stdout/stderr, timestamps, Sandbox IDs, private endpoints, and control job IDs.

`lean_timeout_60m_client_cutoff` means the client had not received a terminal
Judge response by 3,600 seconds.  It does not mean `incorrect` and does not
claim a server-side timeout.

## `results/trace_fluctuation_supplement.jsonl`

Twelve previously generated and reaccepted trace certificates retained as
evidence of compute/load sensitivity.  `counted_in_fresh_round115` is always
false.  Two problems overlap the final fresh trace set, so these twelve files
add ten unique problems to the fresh trace and primary four-family unions.

## `results/accepted_sets.json`

Exact problem-ID sets for the four selected family portfolios, their union,
and the separately excluded trace fluctuation archive.  Completion is a union
of 57 accepted hybrid problems, the generalized E9001325 supplement, and the
three accepted indexed replacements; repeated problem certificates are set
deduplicated.

## `results/test_set_breakdown.json`

Source-specific evaluation of the selected accepted sets.  It reports the
130-record order-five test set separately from the 4,141-record ALPS test set.
For ALPS it distinguishes 4,140 alpha/symmetry equivalence classes from the
4,141 original rows and distinguishes source-native accepted representatives
from duplicate rows covered by an accepted equivalent representative.  The 83
cross-source classes are never added twice, and mapped rows never create extra
Judge receipts.

## Frozen inputs

`inputs/all_4187.jsonl` is the canonical execution benchmark.  Each row carries
`equivalent_record_ids` and `provenance_sources`, which reconstruct the
order-five and ALPS source views without rerunning duplicates.  The historical
name `generalization_4057.jsonl` means representatives outside order five; it
must not be interpreted as the complete ALPS denominator because 83 order-five
representatives also have ALPS provenance.  The other JSONL files are exact
subsets used by supplemental profiles.  `inputs/manifest.json` gives record
counts and hashes.
