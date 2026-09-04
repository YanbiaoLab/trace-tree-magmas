# Austin96 novelty audit

This directory audits the 32 Austin96 identities accepted by the selected tuned
trace, guarded, completion, and CNF profiles against the public ALPS screening
and residual-portfolio result tables. It is a data-only analysis: it runs no
local solver and makes no Judge request.

The audit distinguishes counts of ETP equation IDs from counts modulo duality.
It also separates an exact, reproducible ALPS comparison from a broader literature
search, for which absence of a search hit is not a mathematical proof of priority.

The exact pinned-table comparison yields 28 candidate-new identities in 14
duality classes.  The current manuscript reports the same 28 identities under
its documented literature-and-artifact audit.  This directory independently
reproduces the frozen-table comparison; it does not turn absence from those
tables into an unrestricted proof of historical priority.

See `NOVELTY_AUDIT_REPORT.md` for the conclusion and claim boundary,
`REPRODUCIBILITY.md` for the exact rerun command, and
`CONFERENCE_PREPRINT_NOTE.md` for the arXiv/priority distinction.
