# S038 — Adversarial paper review of EC-C025

Saved BEFORE Lean. Same-agent review, not independent external review.
Paper: proofs/EC-C025_RAW_CLOCK_EXTENSION_BOUND.md. No local gap found.

| Attempted falsification | Resolution |
|---|---|
| n=0 changes history at the same board | Only refl(s) generates zero, retaining the exact State. |
| One quiet ply needs two clock units | Frozen append_clock increments by exactly one board ply. |
| Reset edge breaks the induction | Frozen append_clock_le includes child zero; nonnegativity suffices. |
| Mixed quiet/reset path loses count | Index advances on every actual append, even when counter resets. |
| Equal erased boards allow unrelated histories | Successor requires RawBoardStep equality to append of the actual prior state; Legal erasures alone are insufficient. |
| Move or legality witness is absent | Each RawBoardStep supplies m, hm and exact append equality. |
| Earlier raw draw stops the bound | No ongoing/terminal guard; theorem is raw, not FIDE admissibility. |
| Reset truncates repetition evidence | Frozen append_spec retains complete moves/positions on every edge. |
| Root seeded with an arbitrary KRK clock | State retains initial-rooted Trace; clock is its fold, no seed parameter. |
| Every k≤n prefix asserted without proof | Only represented prefix subderivations are discussed; no extra extraction theorem is claimed. |
| Current bound defeats all intended claims | Rejected: h+n<100, all-defender prospective children and repetition controls remain separate. |

The induction uses only actual append_clock_le, monotone addition and
transitivity; no endpoint-clock hypothesis or erased-board surrogate occurs.
Both colours, every material and every actual legal move are quantified.
Symbolic cases only; no fixed full game prefix or finite diagnostic claimed.
Classical construction. Verdict: LOCAL_VERIFIED for the exact raw bound;
Gate F and any later Gate Z require their own observed evidence.
