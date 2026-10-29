# Seven-ply strong forcing at the second edge square

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For weak king W=(2,0), a nonchecking strong-turn KRK board with distinct
pieces and king separation at least two forces mate within seven plies
exactly when either of the following holds:

* The strong king can move one square to one of (1,2), (2,2), (3,2),
  with the original rook in that destination's evaluated six-ply region.
* K=(1,2) and R has file 3, rank at least 3, or rank 2 and file at
  least 2; or K=(2,2); or K=(3,2).

The first alternative is a catalogue of three fixed king points, with
symbolic rook inequalities. `KRKSevenSecond.RookRegion` spells out the
three six-ply rook regions. Each guarantees separation, distinctness,
rook safety and a legal weak reply. No unevaluated legal-move search is
used in the criterion.

For necessity, the existing seven-ply entry theorem excludes castling
and reduces every nonmating first move to an ordinary king or rook
entry into the six-ply region. The six-ply second-edge geometry forces
one of the three king points. For (1,2), a rook initially on rank 2
to its left is blocked from file 3 by its king, giving the stated
rook-line condition. At the other two points every admitted nonchecking
rook admits a suitable entry.

For sufficiency, `rook_destination` constructs that entry by rank and
file inequalities. In particular, a rank-1 rook at K=(2,2) enters file
3 or 4 on rank 1; a rank-2 rook moves to rank 3; a higher rook moves
along its rank. At K=(3,2), enter file 1 at rank at least 2 or rank 1
at file at least 4. Each constructed move is checked for both blockers.
Immediate mates enter the middle king point and are retained.

`kernel_seven_iff` quantifies over actual native flags. The theorem is
clock-free and unfrozen; it is an ingredient for eight-ply edge geometry,
not a complete history or KRK classification.
