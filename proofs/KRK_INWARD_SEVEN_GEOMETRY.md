# Exact inward-corner seven-ply geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Take W=(1,1), separated kings, distinct occupied squares, strong turn,
and no current rook check on W. The complete strong seven-ply criterion
is the union of four branches:

* rook rank 2, rook file at least 3, king one step from (3,1);
* rook file 2, rook rank at least 3, king one step from (1,3);
* king (3,1), with rook rank 2, or rook file at least 4, or rook file 3
  and rank at least 3;
* the transpose of the preceding branch, with king (1,3).

The first two branches are king entries into the two fully evaluated
inward-corner six-ply regions. Their rook restrictions already guarantee
destination distinctness, safety and a live weak reply. The final two
branches evaluate all rook-line entries into those same regions.

For example, when K=(3,1), source R=(3,0) cannot enter the horizontal
six-ply region in one move: its own king blocks the vertical path to
rank 2. Source R=(3,2) can move horizontally to (4,2); remaining on its
current target square is not counted as a move. The stated inequalities
include both boundaries.

Necessity extracts the first nonmating ordinary move from the complete
seven-ply entry theorem and the two six-ply destination shapes. Immediate
mate is impossible on the interior. Sufficiency constructs the king or
rook move explicitly; transposition reuses the horizontal argument for
the vertical branch. No enumerated position values are used.

`KRKSevenInner.kernel_seven_iff` gives the native kernel equivalence under
the stated assumptions, with actual flags retained. `clear_iff` gives
the geometric correspondence. `inner_entry_necessary` is the weaker
projection used by the exact eight-ply near-strip necessity proof.
These are clock-free supporting results and remain unfrozen; they do not
settle all incoming-history outcomes or complete KRK.
