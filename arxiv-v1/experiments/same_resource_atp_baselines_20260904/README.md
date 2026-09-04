# Same-resource ATP baselines (2026-09-04/05)

This artifact contains the corrected same-resource ATP comparison for
Trace-Tree Magmas. All solver processes ran in remote sandboxes; no ATP binary
was executed on the controller host.

## Frozen protocol

Each problem received one 120-second solver allowance, a 2-vCPU/2048-MiB
sandbox, and a 2000-MiB sampled aggregate process-group RSS limit. RSS was
sampled every 0.05 seconds. The requested sandbox concurrency was 150; the
effective pools are recorded in `EXPERIMENT_RUN_REPORT.md`.

The released solvers and commands are:

- Vampire 5.0.1: CASC portfolio, conjecture-proving (`triv`) direction.
- E 3.5.1: `--auto`, conjecture-proving (`triv`) direction.
- Twee 2.6.1: ALPS-aligned parameter-free completion,
  `twee --tstp --formal-proof problem.p`. `--formal-proof` changes retained
  output only; the search flags relative to ALPS are empty.

## Primary results

The two benchmark views are reported separately because 83 Austin96 inputs
also occur in ALPS4141.

| benchmark | records | tool | theorem | trusted counter-satisfiable |
|---|---:|---|---:|---:|
| order5 | 130 | Vampire | 0 | 0 |
| order5 | 130 | E | 0 | 0 |
| order5 | 130 | Twee complete | 2 | 18 |
| ALPS4141 | 4141 | Vampire | 28 | 0 |
| ALPS4141 | 4141 | E | 54 | 0 |
| ALPS4141 | 4141 | Twee complete | 79 | 4 |
| ALPS4141 | 4141 | three-tool union | 94 | 4 |

On order5, the 18 trusted Twee counters comprise all 10 known Austin laws,
six members of the 96-candidate group (E12857, E19966, E22619, E22634,
E26105, and E33436), and E17260/E28740 from the 24 finite-status-unknown
group. The two Twee theorems are E40037 and E5834.

The concatenated execution matrix has 4271 record IDs and 12,813 tool/problem
rows. It is an audit view, not a third benchmark denominator. Record-ID unions
are 96 theorems and 22 trusted counters. Exact directed-implication
deduplication gives 4188 problems, 94 theorems, and 18 counters; alpha-renaming
plus equality symmetry gives 4187 problems with the same decisive unions.
There are no theorem/counter conflicts.

## Counter-status boundary

Vampire/CASC and E/auto are incomplete proving-mode searches here. Their raw
`CounterSatisfiable` text is preserved as diagnostic evidence but receives an
empty scientific verdict. Only a clean parameter-free `twee_complete`
saturation can produce `counter_satisfiable_trusted=true` and
`scientific_verdict="AUSTIN"`. This establishes a nontrivial model of the
source law, not finiteness, infinitude, an explicit model, or a Lean
certificate. See `COUNTER_SATISFIABLE_POLICY.md`.

## Contents and verification

- `config/`: frozen commands, limits, versions, hashes, and upstream sources.
- `inputs/`: the three source datasets and frozen concatenation.
- `results/atp/`: sanitized per-problem rows, decisive/raw-counter evidence
  streams, source splits, overlap tables, and resource distributions.
- `results/input_overlap/`: independent source-overlap audit.
- `results/alps_etp_coverage/`: ALPS layer/membership audit.
- `scripts/`: remote runner, independent parser, postprocessor, and verifiers.
- `judge_canary/`: a separate Judge-v3 availability canary; ATP output itself
  is not submitted to Judge v3.

Run from this directory:

```text
python scripts/verify_results.py --experiment-root .
python scripts/verify_public_artifact.py --root . --check
```

Both commands are read-only. The first reconstructs scientific statuses from
the retained raw evidence streams and recomputes all frozen counts.

