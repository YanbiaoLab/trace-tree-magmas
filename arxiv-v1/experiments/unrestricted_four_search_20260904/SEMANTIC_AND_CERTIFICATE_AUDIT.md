# Four-search semantic and certificate audit

## Shared invariant

Each solver searches for a magma that satisfies the source equation and refutes
the target equation.  A generated result is counted only through the exact Lean
module submitted to Judge v3.  Direct, dual, and generalized orientations are
transported back to the original problem before constructing `Goal`.

## Trace

The trace model uses free `e`/`k`/`p` syntax plus a finite `Code` relation and a
raw-or-hit `Step`.  Generated proofs establish table functionality, exclude
raw/table conflicts through structural size bounds, prove the source trace, and
exhibit an `e`/`k e` target witness.  The final v5 compiler incorporates the
earlier equality-transport and exact linear-bound fixes.  Python term
normalization, trace expansion, active masks, source execution, target miss,
and Lean constructors were checked for agreement.  Judge accepted every one of
the 636 fresh full-run certificates.

## Guarded

The guarded decoder operates on disjoint syntactic regions of the same free
tree syntax.  Constructor/guard cases establish functionality and the source;
a constructor-disjoint witness refutes the target.  The two final certificates
are accepted.  The carrier is mathematically infinite through the `k` tower,
but the current guarded certificate does not separately expose a
`tower_injective` theorem.  Accordingly, this artifact claims a Judge-checked
countermodel verdict, not an additional Lean theorem explicitly asserting
infinitude for this family.

## Completion

Completion orients equations by a well-founded order, closes critical pairs,
and checks variable closure, decreasing rules, nonlinear peaks, source closure,
and the target witness.  `NF` is the subtype of irreducible free terms; `eval`
uses the functional completed rule relation or a raw pair.  Regular and indexed
certificates are two proof representations of the same completed-rule model.

The v5 selector avoids the prior indexed-DAG proof defect on occurs-cycle leaves
and removes the earlier certificate heartbeat cap for large dependent case
products.  Previously rejected E4916/E41082 and the former heartbeat cases were
targeted and accepted before the final regression.  In the final regression
there are no rejections.  Three hybrid modules exceeded the experiment's
60-minute client wait, and accepted indexed-profile modules for the same three
problems are included instead.  This is a proof-performance substitution, not
an extra solved-problem count.

## CNF NF16

CNF proposes a bounded set of functional rewrite-table rules and compiles them
to `Code`, `NF`, and `eval`.  The sound v3 repair enforces pair-left-side rule
validity at orientation, seed, admission, source-tableau, target-witness, and
Lean-compilation boundaries.  This eliminates the Python/Lean mismatch found in
older variants.  All 17 regenerated sound NF16 certificates were accepted; all
older affected CNF results are excluded.  The emitted sound CNF certificates
also contain an injective `k` tower proof.

## Final conclusion

No remaining search/Lean model-semantics mismatch was found in the selected
code.  The final public result has zero non-timeout Lean rejection.  The only
non-accepted generated occurrences are the three explicitly classified
completion-hybrid client-policy timeouts, each covered by an accepted alternate
certificate from the indexed profile.
