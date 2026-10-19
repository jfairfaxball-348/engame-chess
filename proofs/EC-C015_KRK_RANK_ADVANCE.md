# EC-C015 — A direct distant-rook rank contraction

S028, standalone Gate L argument, 2026-10-19. Classical rook/king geometry, no novelty claim. Either strong colour, arbitrary flags, exact KRK and strong turn; coordinates 0…7.

Assume S.rank<R.rank, R.rank+2≤W.rank, and |R.file−W.file|≥3. Choose C=(R.file,R.rank+1). It is on board because R.rank+2≤W.rank≤7. Move the rook R→C.

The chosen move is legal: it is a nonzero vertical rook move; S is strictly below its source, W strictly above its target and on a different file; neither can obstruct the segment or occupy the target. The kings' rank difference is at least three. EC-T0007's geometric-model soundness therefore supplies an actual kernel-legal successor, with arbitrary flags preserved as dictated by the kernel move. The chosen rook is safe by file distance at least three.

There is a legal lone-king reply: choose a horizontal neighbour on the board (right unless W is on h-file, then left), keeping W's rank. The file margin is still at least two; the kings stay at rank distance at least three; neither a rook rank nor rook file attacks the target. This is an explicit witness, so the universal reply theorem is not vacuous or a stalemate claim.

For **every** kernel-legal reply, EC-T0010 extracts a non-capturing unit king step W→V and confines V strictly above C.rank. The file margin after that step is at least two. Thus the result is strong-turn KRK with `DistantBarrier S C V`. All replies keep the rook safe against an immediate capture. The new barrier rank is exactly one greater; the number of squares in the upper rank strip falls from 8*(7−R.rank) to 8*(7−C.rank), a decrease of eight. This is a two-ply local contraction, not an assertion that the same move can be repeated indefinitely. Its finite phase length is two; 7−rookRank strictly decreases across this phase.

For a PhaseImage input, this applies to the upper band W.rank=R.rank+2 when the extra three-file margin holds. It does not cover the lower band or a two-file margin. It need not preserve the PhaseImage relation between king and rook, and no universal re-entry/termination policy follows. Safe, nonempty weak nodes are live by EC-T0010; every strong-turn legal KRK arrival is live by EC-T0007. This rules out relying on continuation after a dead-position draw, but liveness is not ForceMate.

## Removing the extra margin by a bounded rescue phase

The upper-band image can have only a two-file rook margin. This does not permit a safe *two-ply* result, but does permit a four-ply contraction with rescue.

Assume the previous rank hypotheses and only |R.file−W.file|≥2. The same rook-up move is legal and initially safe. A horizontal reply exists (even a step toward the rook leaves a different file). Every legal reply preserves KRK and lies above the new rank C.rank. Its rook/file distance can be one, so the rook may be hanging on the resulting **strong** turn; no further weak move is allowed before the prescribed repair.

For such a reply, if its rook distance is at least two, the desired DistantBarrier already holds. Otherwise relocate the rook horizontally along its current barrier rank to a far file: file 0 if the lone king's file is at least 4, else file 7. Its distance from the lone king is at least four. This target differs from the hanging rook's file (whose distance was at most one); neither king obstructs the rank because S is below and V above it. The move is legal, with arbitrary flags. Every following weak reply is non-capturing, remains above the same rook rank and leaves rook distance at least three. A horizontal weak move witnesses nonemptiness; the king rank gap is at least three in the rank-advance application. More generally rank separation of two is enough for that witness.

The policy is explicit: raise, every reply, either finish or far-file rescue, every reply. Its finite phase length is at most four plies; the new barrier rank is exactly old+1 throughout the repair, so 7−rookRank strictly decreases once per completed phase. The brief hanging-rook state is not a lost rook or an assumed safe weak turn: it is a strong-turn state with a prescribed safe legal rook move. The next theorem must retain this branch and quantifier order explicitly. From PhaseImage's upper band, the initial two-file margin follows symbolically from four-file rook/strong separation and at-most-two lone/strong offset.

This covers the entire upper band of the justified image family, but not its lower band and not a closed repeated invariant. No full ForceMate conclusion is asserted.
