# `CounterSatisfiable` interpretation policy

The three ATP runs in this experiment are comparisons of proof-search
behaviour.  A raw SZS status is not automatically a scientific Austin
classification.

| Run | Encoding/search direction | Raw `CounterSatisfiable` treatment |
|---|---|---|
| Vampire 5.0.1, CASC portfolio | `triv`: prove the conjecture `L |= x=y` | Retain raw status and stream; scientific verdict is empty. CASC proving-mode saturation may be incomplete. |
| E 3.5.1, `--auto` | `triv`: prove the conjecture `L |= x=y` | Retain raw status and stream; scientific verdict is empty. This is not the dedicated satisfiability configuration. |
| Twee 2.6.1, parameter-free complete run | `both`, `twee --tstp --formal-proof` | A clean completed saturation is accepted as a trusted Austin result. Search flags match ALPS (`[]`); `--formal-proof` is added only to retain a complete proof block for theorem results. This is the released Twee experiment. |

Consequently, `counter_satisfiable` is a trusted result status only if the
record also has `counter_satisfiable_trusted=true` and
`scientific_verdict="AUSTIN"`.  Among the three primary comparison runs only
the parameter-free `twee_complete` run may set those fields.  A trusted Twee
result establishes that the source implication fails, hence that a nontrivial
magma satisfying the source law exists; it does not by itself assert that the
model is finite or infinite.  Raw Vampire/E sightings use
`raw_counter_satisfiable_seen=true`, `status="completed_no_decisive_result"`,
and `scientific_verdict=""`.

A theorem is accepted only when the solver exited cleanly and a complete
TSTP proof block is present.  In a Vampire portfolio output containing both a
complete theorem proof and an untrusted counter status from another slice,
the theorem is the sole scientific verdict; `raw_status_conflict=true`
preserves the diagnostic fact.

The release verifier independently decompresses every retained evidence
stream and reconstructs these fields.  All raw counter-status streams are
published even though they are nondecisive.  The policy is implemented in
`scripts/remote_worker.py` and independently duplicated in
`scripts/independent_reparse.py`; synthetic tests include untrusted Vampire/E
counters, a trusted complete-Twee counter, and a mixed Vampire portfolio case.

## Frozen provenance

- ALPS `baseline/baseline_probe.py`, SHA-256
  `751cd2c2e8d887ddb26669bbccdaa6f12469e759bb074e1734b8dbc06d132059`,
  is the source of the direction-sensitive `triv` rule.
- Twee `executable/SequentialMain.hs`, SHA-256
  `9b617123da095eb72ecc1510527872391bae24100f040566fbf6accf07601893`,
  supplies the completion/status implementation inspected for this policy.
