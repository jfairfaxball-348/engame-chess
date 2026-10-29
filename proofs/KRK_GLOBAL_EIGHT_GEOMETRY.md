# Complete eight-ply weak geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

`KRKEightGlobal.kernel_eight_iff` gives a full-board clock-free KRK
criterion, with the weak side to move, distinct pieces, separated kings
and actual native flags:

mate within eight plies iff already checkmated or `KRKEightGlobal.Region`.

On the interior, use [the complete interior criterion](KRK_EIGHT_INTERIOR_EXACT.md).
On an edge, the existing coordinate frame maps W to (j,0), 0<=j<=3.
The only possible weak destinations are the five compass points west,
east, northwest, north and northeast. The formulas suppress destinations
that fail the actual geometric guard; at a corner the left coordinate
saturates at zero and introduces only a duplicate or an invalid guard.

`KRKEightEdge.Region` requires a safe rook, at least one legal reply
among those five points, and the evaluated seven-ply destination test
at every legal point. That test is a fixed catalogue:

* (0,0): [corner seven-ply geometry](KRK_CORNER_SEVEN_GEOMETRY.md).
* (1,0) and (0,1): [near-corner seven-ply geometry](KRK_NEAR_SEVEN_GEOMETRY.md), with transposition for the latter.
* (2,0): [second-edge seven-ply geometry](KRK_SECOND_SEVEN_GEOMETRY.md).
* (3,0) and (4,0): the complete middle-edge five-ply formula, since seven equals five there.
* (1,1): [inward-corner seven-ply geometry](KRK_INWARD_SEVEN_GEOMETRY.md).
* All other neighbouring interior destinations: impossible for seven-ply strong forcing.

All destination formulas are previously proved coordinate inequalities,
fixed king-point tests and evaluated rook-line conditions. No winning
predicate, minimax recurrence, position-value atlas or search certificate
occurs in the region. The finite reply quantifier has exactly five
geometric compass cases; it does not enumerate KRK positions.

`kernel_exact_eight_iff` gives the matching optimal-distance criterion:
the nonterminal eight-ply region holds and the full six-ply criterion
fails. Weak-turn seven equals six, excluding every shorter alternative.
Mate precedence and nonempty weak replies are retained explicitly.

This settles eight-ply **board geometry**, not the full next clock band:
original incoming-history barriers still matter. It also does not settle
lower-clock outcomes, full FIDE correspondence or global WDL/DTZ. All
new results remain unfrozen.
