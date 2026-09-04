# Experiment run report

## Execution outcome

All 12,813 tool/problem rows reached a scientific or resource terminal state.
There are no released infrastructure-error, output-limit, incomplete-proof, or
conflicting-decisive rows. Every owned sandbox was released.

| tool | ready pool | campaign wall time | theorem | trusted counter | memory limit | time/resource limit | other clean nondecisive |
|---|---:|---:|---:|---:|---:|---:|---:|
| Vampire 5.0.1 | 131 initially; targeted retries | 5947 s main run plus retries | 28 | 0 | 3210 | 935 | 98 |
| E 3.5.1 | 150 | 3592 s | 54 | 0 | 1 | 4201 | 15 |
| Twee 2.6.1 complete | 141 | 3487 s | 81 | 22 | 852 | 3316 | 0 |

The Vampire final file is the deterministic merge of the full campaign and
exact-ID infrastructure retries. A cleanup audit was corrected to ignore
already-dead zombie process entries; the remaining nine affected records were
rerun and all ended at the memory limit. Independent parsing accepts the final
4271 rows. E had one and Twee had two transient sandbox failures, all retried
inside their campaigns with no missing terminal record.

## Benchmark-separated results

| benchmark/tool | theorem | trusted counter | raw untrusted counter |
|---|---:|---:|---:|
| order5 / Vampire | 0 | 0 | 14 |
| order5 / E | 0 | 0 | 14 |
| order5 / Twee complete | 2 | 18 | 0 |
| ALPS4141 / Vampire | 28 | 0 | 86 |
| ALPS4141 / E | 54 | 0 | 1 |
| ALPS4141 / Twee complete | 79 | 4 | 0 |

The ALPS4141 theorem union is 94. The four ALPS4141 trusted counters are exact
duplicates of order5 E19966, E22619, E22634, and E26105. They are not four
additional mathematical problems.

## Audit results

- Independent parser: Vampire 4271/4271, E 4271/4271, Twee 4271/4271.
- Decisive rows: 28, 54, and 103 respectively.
- Record-ID union: 96 theorem, 22 trusted counter, zero conflict.
- Exact problem union: 94 theorem, 18 trusted counter, zero conflict.
- Alpha/equality-symmetry problem union: identical decisive counts.
- Public privacy-pattern hits: zero before manifest generation.

Detailed solver-time, wrapper-time, cleanup-time, and process-group RSS
distributions for all, decisive, and nondecisive rows are machine-readable in
`results/atp/summary.json`.

## Interpretation limit

The ATP experiment produces no explicit infinite carrier and no Lean-checked
model certificate. ATP non-success is only a budgeted observation. The 28 new
Austin classifications in the main artifact rely on separate explicit-model
searches and Judge-v3-accepted Lean certificates, not on ATP failure.
