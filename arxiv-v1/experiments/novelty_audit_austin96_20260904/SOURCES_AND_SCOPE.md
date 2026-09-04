# Sources and audit scope

## Pinned machine-readable sources

ALPS repository:

- URL: https://github.com/EricX22/ALPS
- commit: `e831af76da026edfa1697c970aeebb8098507b6d`
- commit time: 2026-08-16T09:18:49-04:00
- paper v1: https://arxiv.org/abs/2608.15979 (2026-08-17)

Files compared:

- `corpus/austin_laws.jsonl`
- `corpus/final_status.jsonl`
- `corpus/evaluation_pool.jsonl`
- `baseline/baseline_full_final.jsonl`

Their content hashes, together with the Austin96 input and our complete result
file hashes, are recorded in `results/source_hashes.json`.  No private path,
credential, token, account identifier, or service endpoint is recorded.

## Public contextual sources

- ETP order-five Austin table:
  https://teorth.github.io/equational_theories/blueprint/order-5-austin-laws.html
- ALPS automated frontier and appendix:
  https://arxiv.org/html/2608.15979#S4.SS1
  and https://arxiv.org/html/2608.15979#A1
- ETP project paper:
  https://arxiv.org/abs/2512.07087
- Janota Vampire report:
  https://arxiv.org/abs/2508.15856
- Janota--Rawson--Schulz case study:
  https://arxiv.org/abs/2602.16324

## Matching rule

The audit parses both ETP and ALPS laws as binary term trees and canonicalizes
variables by first occurrence across both sides of the equation.  It therefore
matches consistently alpha-renamed laws without treating mere whitespace,
operator glyph, or variable-name differences as different identities.

The novelty unit is the exact normalized ETP equation ID.  Dual laws remain
two IDs in the headline count and are also reported as one duality class.

