# Austin96 novelty audit report

Audit updated: 2026-09-04

## Machine-checked conclusion

The tuned selected searches have Judge-v3-accepted certificates for 32 of the
96 Austin candidates. Exact normalized-law matching against the pinned ALPS
screening and residual-portfolio tables finds four overlaps: E19966/E26105 and
E22619/E22634. The exact pinned-table difference is therefore **28 ETP equation
IDs in 14 duality classes**.

This is a reproducible comparison with frozen machine-readable tables, not by
itself a universal proof of historical priority.  The current manuscript's
28-identity claim additionally relies on its dated literature-and-artifact
audit.  That broader audit and the exact table subtraction are complementary
evidence and should not be conflated.

## Exact reconciliation

| Quantity | Law IDs | Modulo duality |
|---|---:|---:|
| Selected-search accepted Austin96 identities | 32 | 16 pairs |
| Overlap with pinned prior ALPS positives | 4 | 2 pairs |
| Candidate-new relative to the pinned tables | **28** | **14 pairs** |

ALPS has six positive Austin96 IDs in total:

- screening: E12857, E33436;
- residual portfolio: E19966, E26105, E22619, E22634.

Our selected searches cover the four residual-portfolio IDs but not the two
screening IDs. Thus subtracting all six would be wrong; the exact intersection
has four IDs.

## The 28 candidate-new IDs

The 14 dual pairs are:

1. E4952 / E41252
2. E4957 / E40914
3. E5012 / E41253
4. E5066 / E41239
5. E5141 / E40917
6. E5295 / E40909
7. E7701 / E38303
8. E7755 / E38249
9. E9345 / E36713
10. E9384 / E36714
11. E9667 / E36638
12. E9680 / E36524
13. E11081 / E35036
14. E11116 / E34888

The machine-generated table is `results/candidate_new_dual_pairs.csv`.

## ALPS coverage boundary

It is inaccurate to say that all 28 are rows of the released ALPS hard pool.

- 24 occur in `corpus/evaluation_pool.jsonl` with `tier="hard"` and
  `baseline_resolution=null`.
- E4957, E5012, E40917, and E41252 are absent from ALPS's screened corpus and
  residual evaluation pool.

Across the full Austin96 set, 87 IDs occur in `final_status.jsonl` and 83 in
`evaluation_pool.jsonl`. The exact frozen ETP and ALPS comparison is the
reproducible core; absence from a web search is supporting evidence only.

## Claim wording

Directly certified by this machine audit:

> Against the pinned pre-release ETP/ALPS machine-readable tables, the tuned
> selected searches certify 32 Austin96 identities, four of which were prior
> ALPS positives, leaving 28 candidate-new identities (14 duality classes).

The current manuscript uses the stronger phrase “first certified infinite
models for 28 identities” under its separately documented, dated
literature-and-artifact audit.  This release preserves the exact pre-result
tables and hashes needed to reproduce the machine-checkable portion of that
claim, while retaining the standard caveat that an absence result from a
literature search is not a mathematical theorem.

## Priority after mutable upstream updates

If ETP later incorporates these certificates, use the dated pre-result
snapshot, arXiv timestamp, repository commit and artifact hashes to establish
chronology, and acknowledge the updated ETP page rather than describing it as
still open.
