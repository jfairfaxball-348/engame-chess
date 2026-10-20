# S046 — Adversarial paper review for EC-C029

Saved BEFORE Lean. Same-agent review, not independent external audit.
Paper: proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md. Exact local proof has no gap.

| Attempted falsification | Resolution |
|---|---|
| Distinct files but dx=0 after coercion | Equality of Int casts gives equal Nat values; Fin.ext contradicts file inequality. |
| Straight single/double pawn move accepted as EP | Both require dx=0, excluded by the file argument. |
| Ordinary pawn capture masquerades as EP | Empty destination makes ordinary occupied-destination branch false. |
| Nonpawn changes files into an empty square | Source Pawn premise excludes it. |
| Wrong/missing ep flag or flank pawn still legal | All alternative pawnMoveOK branches eliminated, remaining EP branch requires those fields. |
| Self-check/pinned ep treated as legal | Original actual isLegal retained; pseudo-legality alone never suffices. |
| Promotion field ignored or side fixed | Exact Move and isLegal retained; both colours share branch proof. |
| Raw malformed flag claimed to have lawful ancestry | Rejected: raw universal kernel domain, not a FIDE history theorem. |
| New event fields silently assumed on RHS | Flag/flank recovered, not premises. |
| Result asserts full ep normalization or repetition semantics | Rejected: those remain separate obligations. |

Only source specialization, Boolean branch analysis and finite-file integer
injectivity. No coordinates/positions enumerated or compatible full game/pin
example claimed as executed. Classical result, no novelty/tablebase/engine.
Verdict LOCAL_VERIFIED for the exact characterization; Gate F pending.
