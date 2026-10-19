# S026 fidelity audit — distant safety and four-ply checking progress

New proof modules only: `Rules/KRKForcing/Safety.lean`, `CheckProgress.lean`, `Examples.lean`. Existing proof and definition modules remain unchanged. Core-only Lean 4.35.0.

| Mathematical obligation | Lean declarations | Boundary |
|---|---|---|
| Distant OR protected rook excludes captures in every legal weak reply | `SafeRook`, `krk_safe_reply` | Starts with arbitrary kernel `Legal`; uses king move distance or post-move self-check, not cooperative model soundness as a completeness assumption. Initial check and any flags allowed. |
| Broader separating-rank invariant | `DistantBarrier`, `krk_safe_rank_reply` | Pure `rook_rank_barrier` from EC-T0009 applied after capture exclusion. No nonempty-reply assumption is silently supplied. |
| No continuation after a dead draw | `krk_safe_weak_live` | With an actual legal safe reply, its strong-to-move KRK successor is live by EC-T0007; prepend the mating path. This bridge applies to safe/nonempty weak nodes in the phase. |
| A legal checking action from the exact entry family | `opposition_check_step`, `krk_opposition_check` | Opposed kings are same-file, two ranks apart; checking rook is at least four files away and moves vertically onto the lone king's rank. |
| Every first reply goes up one rank | `opposition_reply_up` | Lower destinations are covered by the strong king; same-rank destinations by the rook. Uses arbitrary-reply completeness from the new safety module. |
| Mate at the top edge, and no earlier stalemate | `opposition_edge_mate`, `opposition_up_reply_exists`, `krk_opposition_edge_force` | Edge: actual kernel checkmate, correct winning colour, chosen legal move. Nonedge: explicit upward weak move exists. No clocks/repetition claim. |
| Follow-up king move and nonempty second reply set | `follow_horizontal_reply`, `krk_follow_check` | Strong king steps one rank up. A horizontal weak step is always available; both file-edge branches proved symbolically. |
| Four-ply all-defences progress | `krk_opposition_four_ply` | Explicit chosen check; arbitrary first reply; chosen king-up; arbitrary second reply. Final strong-to-move KRK has DistantBarrier and smaller `7 - weakRank`. No unproved continuation appears as a hypothesis. |

The pure geometry uses symbolic coordinate inequalities and `omega`; `maxHeartbeats 2000000` is an elaboration budget only. No material-class enumeration or stored values enter any general theorem. Fixed kernel examples are in `Examples.lean`: positive edge forcing; a two-file margin permitting second-reply rook capture; a three-file margin leaving the rook hanging; and a legitimate wide-rook phase whose final kings are not opposed. `maxRecDepth 8192` applies only to fixed examples.

Local diagnostic `scripts/krk_check_phase_diagnostic.py` uses the existing independent ray-walking move generator on 24 chosen configurations, both colours, and their local two-reply trees. It does not call the generator's class-wide diagnostic/fixpoint routine. Observed: 8 mating configurations, 44 first replies and 194 second replies, plus both failed-margin controls. This is error finding, not proof.

## Verification boundary at the proof-source commit

All three new modules compiled locally, including the combined four-ply theorem. Exact-source clean Gate F build and axiom report are required before FORMAL_VERIFIED promotion; the S026 closeout and evidence directory will record the observed result and proof-source SHA. No general rook winning strategy or EC-C011 solution is claimed. Setup/re-entry into opposition remains unproved, as shown by the returned-state witness.
