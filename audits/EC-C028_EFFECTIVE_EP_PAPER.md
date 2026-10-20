# S044 — Adversarial paper review for EC-C028

Saved BEFORE Lean. Same-agent review, not independent external review.
Paper: proofs/EC-C028_EFFECTIVE_EP_TARGET.md. Exact local statement has no gap.

| Attempted falsification | Resolution |
|---|---|
| Raw ep flag absent but availability true | Each actual witness requires q.ep=some m.dst; contradiction. |
| Raw flag present with no eligible pawn/move | Availability false, effective target none. |
| Pseudo-legal pinned ep enables target | Predicate requires actual isLegal=true; no legal witness means none. |
| Two legal source pawns disagree on target | Both flags equal q.ep; some injectivity forces equal destinations. |
| Available branch still returns none | Witness supplies q.ep=some dst, ruling out none. |
| Occupied destination/wrong pawn/colour/flank accepted | Exact event clauses exclude them; ordinary non-ep moves do not qualify. |
| Effective some dst has no actual move witness | Choose availability witness and transport its destination via flag equality. |
| A local play let was treated as exported | New predicate explicitly writes its event; epCapture is not imported as a declaration. |
| Spec implies every raw flag has lawful history | Rejected: arbitrary raw q domain, no FIDE admissibility/history claim. |
| Noncomputable existence treated as executable search | Explicitly classical/noncomputable, no enumeration/dependency claimed. |
| Effective target alone solves repetition/claims | Rejected: full key/Article9.2.3/rights-history and claim semantics separate. |

Case split on actual availability and flag consistency proves both halves.
All controls symbolic, no pinned board or full compatible promotion/ep/castling/
threshold game executed or asserted. Classical construction, no novelty,
tablebase/engine/enumeration. Verdict LOCAL_VERIFIED; Gate F pending.
