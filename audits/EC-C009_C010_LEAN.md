# S024 formal fidelity audit — EC-C009 and EC-C010

## Source and scope
New modules only: `ForcingDefinitions`, `ForceMate`, `KRKConfinement`, `KRKForcingExamples` under `formal/EndgameChess/Rules/`. Frozen modules are imported unchanged. The aggregate and axiom-report entry points gain imports/reports. Toolchain remains core-only Lean 4.35.0.

## Correspondence

| Paper obligation | Lean declaration | Fidelity check |
|---|---|---|
| Named winning colour, zero-ply opponent mate | `MateGoal` | Requires opposite side to move and actual kernel `MatedK`. |
| Finite-rank alternating reachability | `MateWithin`, `ForceMate` | Successor constructor expands to winner existential or nonempty defender universal; move clauses include nondeadness. Budget is plies. No separate policy representation/equivalence is asserted. |
| Increasing fuel cannot destroy a win | `mateWithin_mono_step`, `mateWithin_mono` | Symbolic induction on fuel; no position enumeration. |
| Forcing certificate contains an actual path to the correct mate | `mateWithin_sound`, `forceMate_not_dead` | Prefixes kernel `Legal` moves into kernel `ReachK`. In the defender case uses the explicit nonempty witness. |
| Terminal inversion, dead-reply obstruction | `forceMate_no_moves_iff`, `dead_reply_not_forceMate`, `stalemate_not_forceMate` | No vacuous stalemate win; a dead successor refutes the universal continuation. |
| One-step closure and finite branching | `forceMate_choose`, `forceMate_defend` | List induction combines successor bounds; `mem_legalPositions` is the proved kernel generator correspondence. This uses the finite legal moves from one position, not stored values or enumeration of a material class. |
| Every legal protected-rook reply is covered | `krk_protected_reply` | Starts with arbitrary kernel `Legal`, identifies the unique moving lone king, excludes castling by no lone-side rook, and excludes rook capture by post-move strong-king attack. Returns `Matches` and `StepM.lone`. It is a completeness result on these hypotheses, not an assumption that model soundness alone covers all replies. |
| Rank barrier | `rook_rank_barrier`, `krk_protected_rank_reply` | A one-square step crossing from above must land on the rook rank, which is attacked since the strong king lies strictly below it. Exact `IsKRK` and arbitrary flags in the kernel statement; both colours uniform. |
| First attempted progress scheme fails | `protected_rank_raise_unprotected` | Rank increase with the strong king fixed below the old rank gives distance at least two. No full forcing/descent theorem follows from confinement. |

## Kernel-checked configurations

`krk_optional_capture_counterexample` proves legal Kxb3 and Ka1 from Kh8/Rb3/Ka2, the capture successor dead via EC-T0003, the other successor live via EC-T0007, the starting state live, and White not forcing. `optional_capture_holds` excludes forcing for either colour after the capture. No initial-position reachability claim.

`krk_force_mate_in_one_example` supplies a positive one-ply forcing witness, zero-ply terminal mate, and rejects a win for the wrong named colour. `protected_rank_stalemate_example` satisfies the geometric invariant but rejects forcing for either colour. `blocked_rank_counterexample` shows why the strong king must be strictly below the barrier, not on it.

`decide` is used only for fixed configurations; the general theorems use symbolic proofs/induction and `omega`. `maxRecDepth 8192` affects only elaboration of two fixed examples and does not alter the kernel or trusted axioms.

## Verification status at source commit
The working modules and aggregate compiled successfully. Three deliberately false fixed-configuration claims were rejected (blocked rook ray is illegal; optional declining move is illegal; protected-rank stalemate is check). Source-commit clean-checkout verification, full axiom report and exact proof-source SHA will be recorded in the S024 session evidence and closeout before any `FORMAL_VERIFIED` promotion.

The FIDE-to-model boundary remains A1 and the owner's reviewed general rules encoding. No clock, repetition, full WDL, global strategy equivalence, distance, novelty or independent external-review claim is added.
