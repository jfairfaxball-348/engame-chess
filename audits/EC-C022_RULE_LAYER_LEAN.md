# S033 — Lean fidelity review for EC-C022

Same-agent review, not external independent review. The standalone paper and
adversarial review were saved before the new Lean files. Core Lean 4.35.0,
no dependency change. Paper: `proofs/EC-C022_RULE_LAYER_PROJECTION.md`.

| Paper obligation | Lean source/declaration | Check |
|---|---|---|
| Data independent of σ,n; ordinary interface proofs A–C | HistoryLayer/Definitions.lean, Layer | State is universe-polymorphic Type u; erase, BoardStep, Ongoing, CanClaim precede three proof fields. No winning predicate occurs in these fields. |
| Actual named mate goal | Goal | Exactly frozen MateGoal σ (erase s), with no extra action/ply. |
| Finite board-ply recurrence | RuleMateWithin | Identical terminal/turn structure; strong existential; weak no-claim, explicit nonempty witness and universal BoardStep replies; no ongoing-child restriction. |
| Identical budget projection | Projection.lean, ruleMateWithin_project | Induction on n, generalising s. A handles chosen move and weak witness; B lifts an arbitrary raw Legal r; C handles nondeadness. Child n and parent n+1 unchanged. |
| Uniform forcing corollary | ForcingProjection.lean, ruleForceMate_project | Extract n and reuse it after projection. No pointwise budget or finite-branching substitution. |

The Layer fields apply at every ongoing state and quantify over all destinations.
They are proof parameters, not new global assumptions. Completeness includes
draw-ending legal replies. The defender's no-claim condition is only dropped
when projecting to the less restrictive frozen game. The statement is not a
converse, a holding theorem, or a concrete FIDE instantiation. No KRK geometry,
numerical bound, repetition-key implementation or oracle is introduced.

Three new modules and additive EndgameChess/AxiomCheck entries only. Prior
frozen modules and records must remain byte-identical. Both main statements
and their axiom reports are in AxiomCheck; the full interface and definition
signatures are printed as well. A path-prefix mistake in the first build command
put new files under a nested formal directory; they were moved to the intended
new module paths and empty directories removed. The failed missing-target run
is not a passing verification result. Final module and aggregate builds passed.

Working main declarations have standard-three axiom reports only. Gate F is
pending until a new fresh GitHub clone of the published exact source builds
and its reports/source bytes are checked. No ledger row changes in S033.
