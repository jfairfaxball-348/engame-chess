# S035 — Lean fidelity review for concrete raw traces (EC-C023)

Same-agent review, not external independent review. Standalone paper and
adversarial audit were saved before Lean. Official core Lean 4.35.0, no new
dependencies. Paper: `proofs/EC-C023_RAW_TRACE_APPEND.md`.

| Obligation | Source / declaration | Fidelity |
|---|---|---|
| Actual stored history, fixed root | RawTrace/Definitions.lean, Trace | Indexed Type, not Prop; start at initial only; snoc retains prior Trace, full Move, and isLegal proof at source q. Played endpoint is in its index. |
| Ordered history | Trace.moves / Trace.positions | Prefix plus singleton; positions include initial and each played endpoint, full Position flags/turn included. |
| Concrete state/append | State, erase, initialState, append | State bundles endpoint with matching trace. Append returns exact play and the same stored prefix. No arbitrary seed constructor. |
| Retention / one additional ply | Append.lean, append_spec | Exact played endpoint, complete ordered move/position prefix equations, move-list length +1. |
| Actual step projection | Soundness.lean, raw_step_sound | Extract actual m and isLegal witness from append equality; same witnesses establish frozen Legal. |
| EVERY raw reply lifted | Completeness.lean, raw_step_complete | Arbitrary Legal successor r; its actual Move witness constructs append with erase t=r. No outcome, ongoing, winning or colour filter. |
| Initial-root origin | Origin.lean, trace_arisen | Induction on stored Trace; ReachK.refl at start and ReachK.tail with actual Legal edge at snoc. Raw Arisen only. |

All five modules and the aggregate/axiom runner compile. Four main declarations
have exact #check and #print axioms entries; printed data/definition signatures
expose Type vs Prop, constructor witnesses and the exact root/append relation.
No finite simulation, enumeration or new diagnostic supplies a general theorem.
No additional assumption is introduced for endpoint validity: it is encoded by
the indexed constructor and supplied legal-move proof.

Raw traces deliberately omit clocks, repetition and no-earlier-terminal rules.
They are a concrete move component relevant to abstract Layer A/B, not a full
Layer instance: C, Ongoing, claim and adjudication correctness remain unproved.
All frozen sources/records must stay byte-identical. Gate F remains pending
until the published exact source passes a new fresh-checkout build and full
axiom/source checks. This audit does not freeze any new ledger record.

## Completed Gate F

Published exact source `526a298b80ef04541e518a3dcc62f861c8f51c5c`; ONE NEW fresh GitHub clone without .lake before
build. **59 jobs, exit 0, 360.247s**. Full data/statement/axiom runner exit 0
at `2026-10-19T14:09:53Z`. All 265 reports allowed (234 standard-three, 18 propext/Quot.sound,
8 propext, 5 axiom-free); each new declaration uses only the standard three.
Full working/clean reports and all Lean source bytes match; five-module
forbidden scan zero; 336 protected prior files unchanged. Ledger unchanged,
20 bundles. No unrelated Python diagnostics rerun. EC-C023 FORMAL_VERIFIED,
not frozen; raw-kernel scope only, full FIDE layer remains open. Evidence:
`sessions/evidence/S035/`. Hosted CI unobserved.
