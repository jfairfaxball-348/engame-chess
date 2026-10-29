# No ten-ply weak forcing beyond the first interior strip

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For every board-kernel KRK position with the weak side to move, distinct
pieces and king separation at least two,
`KRKTenInterior.weak_ten_depth_le_one` proves:

mate within ten plies implies weak-king edge depth at most one.

Thus the sixteen central squares at coordinates 2 through 5 are all
excluded, including the four second inward corners (2,2), (2,5), (5,2),
(5,5). Actual native flags are retained. This strengthens the former
eight-ply lower bound; it does not evaluate all ten-ply edge/first-strip
winning regions.

## Nine-ply destination domain

A strong nine-ply nonmating move must enter the complete weak eight-ply
region, which has weak-king depth at most one. The immediate-mate branch
is on an edge. Also, the eight central first-strip squares are outside
the nine-ply strong region, by the previously checked strong ten-ply
exclusion on those squares. Consequently, at a weak ten-ply root every
neighbour of depth at least two or on a central first strip must be
covered by the strong king or rook line. Otherwise that neighbour is a
legal defender escape whose strong continuation cannot force in nine.

The coverage argument retains safe adjacent protected rooks, both
blockers and the actual strict rook ray. `Covered` uses a whole rook
line only as a necessary relaxation; sufficiency is never inferred
from that relaxation.

## Second inward corner

At W=(2,2), the five forbidden destinations are (1,3), (2,3), (3,1),
(3,2), (3,3). Their covering inequalities, king separation and rook
safety force either K file 4 with R rank 3, or its transpose. The
first family always permits escape to (2,1). Transposing the coordinates
puts W at (1,2), K on rank 4 and R on file 3. The complete nine-ply
near-strip criterion then fails: its king entry requires a single king
step to (3,1), while its rook entry requires the king already there.
Neither can hold for a king on rank 4. The transposed prison has the
corresponding escape to (1,2).

`KRKTenSecondCorner.not_clear` proves this exclusion, and
`framed_not_clear` transports it to every second inward corner without
rewriting native histories or rights.

## Remaining central squares

When a central weak square has file or rank 3 or 4, each of its four
axis neighbours lies either at depth at least two or on a central first
strip. Therefore all four must be covered. The same symbolic king/rook
covering inequalities used for the earlier interior escape theorem show
this is impossible for separated kings and a rook distinct from W.
The remaining central squares are precisely the four second inward
corners already excluded. This exhausts the central region by coordinate
inequalities, with no position-value enumeration.

## Actual RAW holding consequence

`KRKTenInteriorHolding.high_clock_deep_holding` proves, for every
admitted RAW strong-turn history at h>=88 with weak king depth at least
two, that both players can hold and the strong side has no actual win.
Any win would have deadline at most twelve. Its first legal strong move
preserves the weak square; weak-turn eleven-ply forcing equals ten-ply
forcing, contradicting the geometric exclusion. Optional claims,
original incoming repetitions and native flags are left intact.

All main declarations pass the local Lean build and axiom audit using
only propext, Classical.choice and Quot.sound. A small local covering
diagnostic was used to inspect candidate prison shapes; the proof is the
symbolic Lean argument and contains no diagnostic outcome data. These
results remain unfrozen, and full KRK closure remains open.
