# Complete seven-ply strong geometry at a corner

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For W=(0,0), the complete nonchecking strong-turn seven-ply criterion is
`KRKSevenCorner.Seven`. It has twelve distinct fixed king destinations
and evaluated rook-line conditions. The seven displayed canonical points
below, together with their coordinate transposes, give the catalogue;
the diagonal points are duplicated by transposition.

| K | Condition for a rook entry into the six-ply region |
| --- | --- |
| (0,2), (1,2), (2,2) | Every admitted nonchecking rook |
| (0,3) | R rank 1, or file 2 or 3 |
| (1,3) | R rank 1, or file at least 2 |
| (2,3) | R file at least 1, rank 1, or rank at least 4 |
| (3,3) | R file 1, rank 1, file at least 4, or rank at least 4 |

For king entries, move one square to one of these points (or its
transpose), with a distinct safe rook satisfying the complete six-ply
corner region and a legal defender reply. `LiveTest` spells out that
last condition as the three possible weak corner destinations. It is
essential: six-ply coordinate membership and rook safety alone do not
exclude stalemate. For example K=(0,2), R=(1,2), W=(0,0) has no legal
weak reply despite satisfying those two conditions.

Necessity follows by eliminating rook-line destinations from each
six-ply corner family. For sufficiency, `rook_destination` constructs a
target in that family. The lower three points use rank-preserving rook
entries or the previously checked diagonal four-ply entry. The higher
points enter rank 1 or file 1 at the listed distances. Every constructed
entry includes distinctness, rook safety and an actual weak reply.
Transposition acts only on coordinates. Immediate mates are included in
the lower-point rook alternatives.

`kernel_seven_iff` checks the equivalence for actual native flags, both
colours, separated kings and a nonchecking strong root. This is a
clock-free result, remains unfrozen and does not close KRK.
