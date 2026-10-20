# S046 — Lean fidelity review of EC-C029

Same-agent review, not independent external audit. Standalone paper/adversarial
review saved BEFORE Lean. Official core Lean4.35.0, no dependency, no failed compile.

One new EPCharacterization module imports frozen RawRepetition.Definitions.
legalEP_iff_shape states EXACTLY frozen LegalEP iff actual isLegal, frozen Pawn,
distinct files and empty dst. No raw ep or flank pawn assumed on RHS.
Forward direction projects frozen clauses. Backward preserves original legality
and source-pawn proof, shows dx≠0 by Fin.ext and exact integer arithmetic (omega),
extracts isPseudo then pawnMoveOK from the specialized source pawn. Simplification
eliminates dx=0 single/double and occupied-dst capture branches; remaining EP
conjunction supplies flag and flank equations used to reconstruct LegalEP.
Both colours, arbitrary raw flags and all actual Move/promotion fields covered.
No enumeration, extra definitions/corollaries, seed, history surrogate or terminal/
material/side/strategy filter. Aggregate import/AxiomCheck additive only.

Incremental lake build passed FIRST attempt (74 jobs); complete AxiomCheck exit 0.
Exact main inspected, [propext, Classical.choice, Quot.sound] only, no warnings.
Symbolic single/double/capture/nonpawn/wrong-flag-flank/pseudo-only-self-check/
both-colour controls; no concrete pinned or compatible full game run/asserted.
No ep-normalization preservation, full repetition key/claims/adjudication or
numerical KRK result. Gate F pending published exact-source fresh verification.
