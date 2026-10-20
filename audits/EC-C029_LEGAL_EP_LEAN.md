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

## Completed Gate F

Own published SHA `421608f5b20fee055bc3cb9d0c5904b0d192527b`; ONE NEW GitHub clone, no .lake before
build. Full 74-job lake build exit 0, 465.649s; COMPLETE AxiomCheck exit 0 at
2026-10-20T09:04:07Z, 276 allowed reports, main standard-three only. Exact main inspected,
whole working/clean output identical, every formal byte matches own anchor.
Full source/transitive hashes and clean HEAD/tree/status retained; one-module
forbidden scan zero. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim. All authoring/fresh
commands passed, no failures or repeated clean build. Gate F complete, Gate Z
pending; hosted CI unobserved. Evidence: sessions/evidence/S046/.
