# Nine-ply strong geometry at an inward corner

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For W=(1,1), distinct pieces, separated kings and a nonchecking strong
root, `KRKNineInner.kernel_nine_iff` characterises forcing within nine
plies by six fixed king destinations and evaluated rook-line conditions.
The three canonical points below and their coordinate transposes are
the complete destination catalogue.

| K | R region for an eight-ply destination | Condition for a rook entry |
| --- | --- | --- |
| (3,0) | R=(x,2), x>=3 | R rank 2 or file at least 3 |
| (3,1) | R=(x,2), x>=2, or R=(1,y), 3<=y<=4 | R rank 2..4, file 2, file at least 4, or file 3 with rank at least 2 |
| (3,2) | R=(2,2), or R=(1,y), y>=3 | R rank at least 3, file 2 with rank at most 1, or R=(0,2) |

A king entry is a single king step to one of the six points, with a
distinct rook in its complete eight-ply region. A rook entry leaves K
at one of the points and applies the last column. The complete
eight-ply inward-corner region supplies safety and a live weak reply.

Necessity follows from the ordinary first-move theorem and elimination
of the rook's destination. The nonchecking-root assumption excludes a
file-1 rook in the displayed orientation. At K=(3,1), a rook on (3,0)
is blocked from rank 2 by its king, producing the stated exception.
At K=(3,2), a rook already on (2,2) cannot make a stationary rook entry,
and rooks farther right on rank 2 are blocked by the king. The last
column therefore excludes them from the rook-entry branch; the overall
criterion still includes any valid king entry from those roots.

For sufficiency, a rank-2 rook moves along that rank to a suitable
destination, or a rook on an admitted file moves to rank 2. At K=(3,1),
the remaining rank-3/4 alternative enters file 1. At K=(3,2), a higher
rook enters file 1, a low file-2 rook enters (2,2), and R=(0,2) moves
horizontally to (2,2). Every ray checks both blockers and nonstationarity.
Transposition affects coordinates only.

Immediate mate is impossible at the inward corner. `kernel_exact_nine`
adds the matching lower bound by subtracting the complete seven-ply
criterion: strong eight equals seven. Native flags remain quantified,
and no incoming history is normalized. This is a clock-free ingredient
for the next weak ten-ply catalogue, not a full KRK outcome or distance
claim. The results remain unfrozen.
