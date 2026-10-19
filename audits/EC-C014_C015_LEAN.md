# S028 Lean fidelity audit — phase image and bounded rank advance/rescue

Same-agent fidelity review, no independent external review. Core Lean 4.35.0, either colour and arbitrary flags. Frozen source modules imported unchanged.

| Obligation | New declaration | Exact boundary |
|---|---|---|
| Six coordinate/image bounds from actual two-reply geometry | `phase_image_of_replies` | Uses `StepM.lone` extracted from an arbitrary kernel reply plus the frozen rank barrier; symbolic coordinate reasoning, not enumeration. |
| Strengthen follow-up and full chosen phase | `krk_follow_check_image`, `krk_opposition_phase_image` | Retains legal ancestry, named colour, exact Matches, both nonempty reply sets and alternating quantifiers; no assumption of an unproved winning continuation. |
| Legal chosen rook raise | `rank_advance_step` | Strong king below source, weak king at least two ranks above it; constructs target one rank up on the same file. |
| Nonempty defending replies | `rank_advance_reply_exists`, `barrier_horizontal_reply_exists` | Explicit horizontal neighbour, both file-edge branches; hypotheses separately ensure rank separation and no rook ray. |
| Two-ply safe contraction | `krk_rank_advance` | Three-file margin; every kernel reply leaves a distant barrier and new rook rank old+1. |
| Rescue a hanging barrier rook | `krk_barrier_rook_rescue` | Exact strong-turn Matches, king below rook and weak king above; only invoked when distance<2. Far-file target has margin≥4 and differs from the current rook. Every reply is covered and nonempty. |
| Whole upper-band image policy | `krk_rank_advance_rescue`, `phase_image_file_margin`, `krk_phase_image_upper_advance` | Two-file margin derived from image; chosen rook raise, every reply, either completed distant barrier or chosen rescue, every reply. At most four plies. The new rook rank is old+1 even after rescue. |
| Adversarial fixed controls | Four declarations in `ReentryExamples.lean` | Legal exact cycle, genuine stalemate, lower-band wall crossing, and raised rook needing rescue. `decide` is confined to these concrete local checks. |

`PhaseImage` is a newly justified output family, not an assumed closed strategy predicate. Coordinates are Fin 8 throughout. `omega` proves symbolic inequalities; heartbeat/recursion settings are elaboration budgets only. The small `position_eq` proof in the cycle uses field equality and finite board extensionality, not an assumption about flags. No native evaluation, proof escapes or new logical axioms are introduced.

Liveness of weak nodes is available via the frozen safe/nonempty bridge, and strong-turn KRK legal successors via EC-T0007; neither is silently upgraded to forcing. The new policy proves a bounded local contraction, not `ForceMate`. The kernel lacks clock/repetition history and the FIDE-to-code bridge remains the existing trust boundary. No full kernel rotation/reflection, tablebase, value fixpoint or class enumeration enters the general statements.

The exact-source Gate F result, declaration counts, source SHA and evidence are recorded in the S028 closeout/evidence after the actual checks. Until those pass, candidates remain LOCAL_VERIFIED. EC-C011 remains PROPOSED because the non-aligned lower-band tempo/pursuit and a recursively closed post-contraction strategy are incomplete.
