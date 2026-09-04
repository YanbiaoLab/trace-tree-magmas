# Provenance

This release artifact was assembled on 2026-09-04 from the final post-repair
remote-Sandbox generation and Judge v3 validation campaign.  The canonical
4,187-problem input has SHA-256
`9454370f95f9876af87414f433d9352c11268957623266edd22f5a99f2493dbc`.

Exact executable hashes and roles are recorded in
`config/variant_manifest.json`.  The final trace, guarded, completion hybrid,
completion generalized, completion indexed, and CNF sources are byte-for-byte
copies of the measured executables.  The input subsets are byte-for-byte copies
of the measured inputs, except `completion_E9001325.jsonl`, which is
deterministically selected from the canonical 4,187 file to remove a redundant
private-staging copy.

The public Sandbox runner is a source-pinned runtime snapshot.  Its adapter only
adds the explicit no-candidate terminal frame, the narrowly evidenced memory
classification, and post-competition 1,000 KiB capture/protocol ceilings.  The
provider domain/template defaults, credentials, private CA, Sandbox instances,
and raw logs are not included.

All published result rows are derived through positive field allowlists.  Lean
modules are materialized from the exact generated certificate strings and
verified against the hashes recorded before Judge submission.
