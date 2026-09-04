# Trace-Tree Magmas

Reproducibility package for:

> **Trace-Tree Magmas: Proof-Producing Infinite Countermodels and 28 New
> Order-Five Austin Classifications**  
> Jiaming Zhao, Bing Wu, and Xu Miao (2026)

The project searches finitely presented operations on an infinite
constructor-tree carrier and compiles every counted model into a self-contained
Lean 4 certificate. This release contains only the experiments used by the
current 28-new-identity manuscript, plus the corrected same-resource ATP rerun.

## Headline evidence

- The selected proof-producing searches have Judge-v3-accepted certificates
  for 32 Austin96 identities. Four were prior ALPS positives; 28 identities in
  14 opposite-magma duality classes are candidate-new relative to the pinned
  ALPS result tables and form the manuscript's novelty set.
- A fresh trace run on Canonical-4187 generated 636 certificates and Judge v3
  accepted all 636. Source reporting remains separate: 36/130 on Order5-130
  and 624 canonical ALPS classes corresponding to 625/4141 ALPS rows.
- Targeted regressions regenerate guarded's 2 historical hits, completion's 61
  problems through one main and two supplemental profiles, and sound CNF
  NF16's 17 hits. The selected four-family union is 668 canonical problems.
- The corrected ATP experiment gives each problem and tool 120 seconds,
  2 vCPUs, a 2048-MiB sandbox, and a sampled 2000-MiB aggregate process-group
  RSS limit. On ALPS4141, Vampire/E/Twee-complete prove 28/54/79 rows and have
  a 94-row theorem union; Twee-complete additionally returns four trusted
  counters. On Order5-130, Twee-complete returns two theorems and 18 trusted
  counters. Vampire/E raw counter text is retained but scientifically empty.

The paper snapshot under `paper/` is the supplied v16 manuscript. Its reported
search and ATP results are synchronized with the verified experiment artifacts
in this release; the machine-readable files remain the authoritative source for
exact per-problem records.

## Release contents

```text
paper/
  supplied v16 manuscript source, generated tables, template files, and PDF
experiments/
  unrestricted_four_search_20260904/    current proof-producing searches
  novelty_audit_austin96_20260904/      current novelty/prior-work audit
  same_resource_atp_baselines_20260904/ corrected three-ATP experiment
verify_all.py
  one-command, read-only verification of all three experiment artifacts
generate_manifest.py
  deterministic regeneration of the repository-wide SHA-256 inventory
SHA256SUMS
  exact repository file inventory and SHA-256 manifest
```

Historical, superseded, incomplete, and stopped experiment directories are not
part of this release.

## One-command offline verification

Python 3.11 or newer is sufficient. The offline verifier does not contact the
network or rerun a search.

```text
python verify_all.py
```

It checks the root manifest; 4271 public four-search rows; all 731 Lean
certificate/receipt pairs and Judge revisions; the 668-problem selected union;
the 32/4/28 Austin96 novelty reconciliation; all 12,813 ATP rows; retained ATP
stdout/stderr evidence; exact and normalized input overlap; and privacy scans.

## Experiment entry points

- `experiments/unrestricted_four_search_20260904/README.md`
- `experiments/novelty_audit_austin96_20260904/NOVELTY_AUDIT_REPORT.md`
- `experiments/same_resource_atp_baselines_20260904/README.md`

Search reruns require the separately distributed remote sandbox runtime and
the pinned solver or Stage-2 environment. Offline evidence verification does
not. ATP solver binaries are never executed on the local controller.

## Licensing and provenance

See `LICENSE.md` for the component-level licensing map and each experiment's
provenance document. Author-created search/verification code and generated Lean
certificates use Apache-2.0; authored measurements and experiment documentation
use CC BY 4.0; Judge receipts and upstream ETP/ALPS inputs retain their own
status and licenses. The manuscript remains all rights reserved except for any
separate deposit license selected by the authors.
