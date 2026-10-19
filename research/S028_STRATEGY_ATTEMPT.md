# S028 — Re-entry attempt and exact remaining lower-band problem

The S026 phase image is now derived from actual legal replies, rather than assumed: rook one rank above the strong king, lone king one or two ranks above the rook, file offset at most two, four-file rook/strong separation and distant rook. The full alternating move/reply statement is retained in EC-C014.

## A completed bounded policy, covering the entire upper band

If the lone king is two ranks above the rook, raise the rook one rank. A three-file rook/lone margin yields a distant barrier after every reply in two plies. With the image's minimal two-file margin, every reply still preserves KRK and the raised rank wall, but one reply can leave the rook hanging. On that strong turn, before any further weak move, relocate the rook horizontally to file a if the lone king is on e–h, otherwise h. Every following reply leaves a distant rook and the same raised wall. The repair is needed only for the unsafe branch and its target is necessarily different from the old rook.

EC-C015 proves this explicit two-or-four-ply policy from the entire upper band, including legal moves, nonempty reply sets and every defence. The barrier potential 7−rookRank strictly decreases. It does not retain the one-rank king/rook gap; thus it is a local contraction, not a complete recursively callable strategy. A hanging rook on a strong turn is deliberately repaired, not confused with a safe weak turn or a completed win.

## Failed lower-band policies with local kernel controls

All coordinates below use ordinary files/ranks. They are locally generated, not tablebase positions.

1. **Lateral chasing cycles.** A legal phase from White Kb1/Rh1, Black Kb3 reaches Kb2/Rh3/Kc4 by Rh3+ Kb4 Kb2 Kc4. Chasing gives Kc2 Kb4 Kb2 Kc4, returning the exact position (including kernel flags/turn). Both strong-turn states satisfy PhaseImage, retain rook safety and have non-opposed files. No strictly decreasing measure can certify termination for this policy. Both cycles are explicit legal moves, not a simulation assumption.
2. **Protected inward rook relocation can stalemate.** Kf6/Ra7/Kh8 satisfies PhaseImage. Rg7 is legal and king-protected but leaves Black not in check and with no legal moves. This state is also a genuine phase image: from Kf5/Ra1/Kf7, Ra7+ Kg8 Kf6 Kh8. Thus confinement and rook protection cannot substitute for a nonempty-reply proof.
3. **Raising from the lower band loses the raised wall.** Ka2/Re3/Kc4, strong turn, is a PhaseImage. Re4+ Kc3 is legal and leaves the lone king below the new rook rank. It is an actual phase image from Ka1/Re1/Ka3 via Re3+ Kb4 Ka2 Kc4. The upper-band premise cannot be dropped.
4. **A two-file upper-band raise can leave the rook hanging.** Ka2/Re3/Kc5 permits Re4 Kd5. The rook is neither distant nor protected; Re4–h4 is the prescribed legal rescue. The input is an actual phase image via Re3+ Kb4 Ka2 Kc5 from Ka1/Re1/Ka3. A branch-sensitive repair, rather than a false immediate invariant, closes this case.

`ReentryExamples.lean` checks the cycle, stalemate, lower-band crossing and unsafe raised-rook/rescue witnesses directly in the kernel. `krk_reentry_diagnostic.py` checks selected two-reply images, raises and rescue branches in both colour orientations with the independent ray-walking generator. It never calls the class-wide graph/fixpoint routine or computes values. These computations support error finding, not either general proof.

## More promising lower-band approach and unresolved proof obligation

For a lower-band state S.rank=R.rank−1, W.rank=R.rank+1, try an oriented pursuit policy which avoids crossing files:

- If files align and a sufficiently safe rook is available, check; use actual all-reply upward geometry, then a possible rook rescue. The frozen four-file entry already handles aligned **image** states.
- With file offset one, use a legal rook waiting move on the same rank rather than moving the king onto the lone king's file. If the reply stays on that rank, it either aligns the files or moves away, increasing offset to two; an upward reply enters the upper band.
- With offset at least two, move the strong king one file toward the lone king, keeping its rank. If the reply stays in the lower band, the sign cannot reverse without an aligned intermediate state. A finite board bounds monotone strong-king file progress.

This suggests a lexicographic measure with remaining file distance to the approached edge as the main component and a bounded normalization/tempo component between king steps. But the safety/tempo bookkeeping is **not proved**: a current two-file rook margin can fall to one after a chasing reply; an extra rook normalization gives the defender another move and may undo the offset progress. Always choosing the extreme far rook file can also yield no actual waiting move when the rook is already there. A distinct second-far file is available with margin at least three, but the move/reply sequence and its measure must be proved together, not assumed to terminate. Crossing through aligned states after a rescue can change the chosen pursuit direction.

A possible way forward is to weaken the checking entry margin to two **in a new module**, prove its one-check/all-reply upward statement and bounded rook rescue, then normalize the chase invariant. EC-T0011's fixed king-up/four-ply theorem still needs four files and must not be edited. Any new policy must explicitly cover every reply, including upward replies during tempo repair, corners, the far-file switch at d/e, nonempty replies and legal ancestry. No full kernel rotation/reflection may be presumed.

The session does not supply a terminating policy from every lower-band image, does not re-establish a recursively closed image invariant after rank contraction, and does not solve arbitrary-arrival safe setup. Those are precise remaining gaps. EC-C011 remains PROPOSED; liveness, local contraction and ForceMate remain distinct. No new frozen ledger row, global WDL, clocks/repetition, distance theorem, seven-piece parity or initial-position claim follows.
