# Unrestricted four-search experiment (2026-09-04)

This is the privacy-safe, self-contained release artifact for the
post-competition trace, guarded, completion, and CNF experiments integrated in
this repository.

The trace run used 4,187 frozen representatives after alpha-renaming and
equality-side-symmetry deduplication.  Primary reporting keeps the two source
test sets separate: the 130 order-five problems and the 4,141-row ALPS pool.
The latter contains 4,140 equivalence classes; 83 classes also occur in the
order-five set, and one ALPS class has two original rows.  Guarded, completion,
and CNF are supplemental methods and were rerun on their historically generated
hit sets.  Those supplemental regressions are not presented as fresh full-test-
set accuracies.

## Headline results

| Result set | Generated | Judge accepted | Policy timeout | Unique accepted problems |
|---|---:|---:|---:|---:|
| Trace v5, fresh full 4,187 | 636 | 636 | 0 | 636 |
| Guarded v1, historical 2 | 2 | 2 | 0 | 2 |
| Completion hybrid v5, historical 61 | 60 | 57 | 3 | 57 |
| Completion generalized v1 supplement | 1 | 1 | 0 | 1 |
| Completion indexed v1 supplement | 3 | 3 | 0 | 3 |
| CNF sound v3 NF16, historical 17 | 17 | 17 | 0 | 17 |

The selected completion portfolio covers all 61 historical completion hits:
57 hybrid certificates, one additional generalized-profile certificate for
E9001325, and indexed-profile certificates for E9000534--E9000536.  Alternate
certificates never count as extra problem hits.

The selected family union covers 44/130 order-five problems.  On ALPS it covers
652/4,140 equivalence classes, corresponding to 653/4,141 original rows.  These
figures are reported separately because 28 accepted classes occur in both test
sets.  The combined deduplicated union of 668 is retained only as an overlap
audit and must not be obtained by adding the two source counts.  There are no
non-timeout Lean rejections.

`results/test_set_breakdown.json` gives per-family counts for both test sets,
the exact 83-class cross-source overlap, and distinguishes direct accepted
representatives from original rows covered through a frozen equivalence class.
Mapped duplicate rows do not count as additional Judge receipts.

## Artifact map

- `algorithms/`: exact source for trace, guarded, all three completion profiles,
  and sound CNF NF16;
- `inputs/`: frozen 4,187 benchmark and exact supplemental subsets;
- `config/`: resource contract, scope, counting rule, and source hashes;
- `results/`: sanitized per-profile rows, source-specific test-set breakdown,
  accepted sets, Judge receipts, and 731 individual Lean certificate files;
- `runner/`: privacy-safe Sandbox runtime snapshot and generation wrapper;
- `scripts/`: candidate preparation, Judge submission, recomputation, manifest,
  and release verification.

## Verify

With Python 3.12:

```bash
python scripts/recompute_summary.py
python scripts/generate_manifest.py
python scripts/verify_release.py
```

See `EXPERIMENT_RUN_REPORT.md` for interpretation and `REPRODUCIBILITY.md` for
the complete rerun sequence.
