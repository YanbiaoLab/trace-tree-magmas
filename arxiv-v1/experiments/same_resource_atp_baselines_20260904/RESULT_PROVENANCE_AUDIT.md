# Result provenance audit

## Binding chain

Each frozen input row contains a stable record ID, source-dataset label, and
two equations. `remote_worker.py` renders the implication as TPTP and stores
its SHA-256 in every result. Each captured stream stores raw byte count,
compressed byte count, and raw SHA-256. Public non-evidence rows remove payload
bytes but retain those bindings.

`independent_reparse.py` reconstructs the TPTP bytes from the frozen input,
checks every problem hash, decompresses all raw private streams during the
pre-release audit, and reconstructs terminal statuses. The released
`verify_results.py` repeats that reconstruction for every published evidence
stream and checks its sanitized counterpart.

## Source and overlap audit

The input files contain 96 Austin candidates, 34 Generality records, and 4141
ALPS evaluation records. Record IDs are unique. Independent tree parsing finds
83 exact cross-source duplicate groups and one additional alpha/equality
symmetry duplicate group, yielding 4188 exact and 4187 normalized problems.

ALPS screened-corpus membership and membership in the ALPS4141 evaluation pool
are separate layers. The frozen ALPS commit is
`e831af76da026edfa1697c970aeebb8098507b6d`; source hashes and the 115/130 versus
83/130 membership audit are recorded in
`results/alps_etp_coverage/summary.json`.

## Semantic audit

The parser gives proof blocks priority only after a clean exit. Earlier
portfolio-slice timeout text cannot mask a later complete Vampire theorem.
Conversely, raw Vampire/E counters never become Austin verdicts. Mixed raw
Vampire theorem/counter output retains `raw_status_conflict=true`, while the
complete theorem is the only scientific verdict. A trusted theorem/counter
conflict would fail the release.

No result claims an explicit model, infinite carrier, independent certificate,
or Judge acceptance. These capability fields are present and all zero.

