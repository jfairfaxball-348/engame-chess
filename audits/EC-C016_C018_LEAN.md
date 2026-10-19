# S029 Lean fidelity audit — finite pursuit and separated rank-wall forcing

Same-agent paper/fidelity review, not external independent audit. Core-only Lean 4.35.0. All frozen and S028 proof modules imported unchanged.

| Obligation | Declarations | Exact boundary |
|---|---|---|
| Explicit safe rook tempos | `wall_far_margin`, `wall_wait_choice`, `krk_wall_rook_move` | Far/second-far target differs from source; margin≥3 before every weak turn, ≥2 after every arbitrary reply. Constructive nonempty horizontal reply; rank wall preserved. |
| Direct coordinate orientation | `pursuitFile`, `pursuit_absDiff`, `pursuit_king_step` | Left/right actual moves constructed separately; no kernel reflection theorem or flags symmetry assumed. |
| Weaker checking family | `opposition_check_step_two`, `krk_opposition_check_two`, `krk_two_file_edge_force` | Two-file margin covers the first check/reply only. Edge is actual named-colour mate; nonedge reply set nonempty. No silent relaxation of the frozen four-ply theorem. |
| Bounded normalization | `pursuit_tempo_return_margin` | Symbolic interval cases prove the offset-two→one→two waiting branch recovers margin≥3 before a chase. Concrete numeral simplification uses kernel-checked `simp +decide`, not native or state enumeration. |
| Terminating lower-band policy | `krk_oriented_lower_pursuit`, `krk_lower_band_force_of_exits` | Conditional `LowerExitWins` is explicit. Exactly one recursive call follows the chosen king-file advance and decreases 7−oriented strong file. Normalization/wait cases are finite proof branches. Every arbitrary reply covered through kernel extraction. |
| Closed continuation and forcing | `krk_rank_wall_force` | Nested strong induction: outer 7−rook rank, inner rook/strong rank gap. Upper and aligned exits are discharged by strictly higher-wall facts; king catch-up strictly reduces gap. Ready case is proved before same-measure far-rook normalization. No circular winning-continuation hypothesis remains in the final theorem. |
| S028 image and setup applications | `krk_phase_image_force`, `krk_vertical_wall_entry_force` | The entire image is now forced mate; a direct vertical setup subfamily also wins. This does not cover arbitrary king axes or all legal arrivals. |
| Concrete positive/negative controls | Four declarations in `WallExamples.lean` | Actual ForceMate on old chase-cycle and threatened-rook walls, two-file edge forcing, two naive setup moves allowing legal captures to KK. Fixed `decide` checks only. |

The main theorem's only hypotheses are exact strong-turn `Matches` and strict rank inequalities `S.rank<R.rank<W.rank`. It does not assume a full strategy, an existing ForceMate result for the same family, a PhaseImage invariant, rook protection, an initial safe-rook margin, or a prior legal arrival. A threatened rook is allowed on the strong turn, where the first prescribed normalization acts. The proof permits no extra weak turn before that repair.

`LowerExitWins` is a structural interface for the separate pursuit lemma, not a redefinition of forced mate. In `WallForce.lean` it is discharged using the well-founded outer rank induction and the two-file checking action. The proof composes the frozen finite-branching `forceMate_choose` / `forceMate_defend`; this supplies a uniform finite bound without claiming a numerical DTM theorem. Finite board edges, nonempty replies and the d/e switch appear in the symbolic proofs.

The existing FIDE-to-code trust boundary, Lean kernel, pinned toolchain and standard axioms remain. Clocks/repetition are absent. No oracle, tablebase, retrograde value, per-position proof table or class-wide enumeration supplies any general theorem. The local Python policy follows coordinate rules and selects immediate replies without value search; its 64 selected mate trajectories are supplementary, not proof of the family.

Exact-source Gate F evidence and the final status are recorded in the S029 closeout/evidence only after the checks run. Until then candidates are LOCAL_VERIFIED. General arbitrary-arrival setup and EC-C011 remain open; the frozen ledger is unchanged.
