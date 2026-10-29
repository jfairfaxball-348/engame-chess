# Complete ten-ply interior geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For every board-kernel KRK position with the weak side to move, distinct
pieces, separated kings and weak king strictly inside the board,
`KRKTenInteriorExact.kernel_ten_iff` evaluates forcing within ten plies.

The weak king must have edge depth one. The existing coordinate strip
frame maps it to (1,j), 1<=j<=3. At j=1 use the complete
[inward-corner ten-ply region](KRK_TEN_INWARD_GEOMETRY.md); at j=2 use
the complete [near-strip ten-ply region](KRK_TEN_NEAR_STRIP.md).
At j=3 forcing is impossible by the
[central-strip exclusion](KRK_TEN_CENTRAL_STRIP.md). Deeper squares are
excluded by the [interior lower bound](KRK_TEN_INTERIOR_LOWER_BOUND.md).
These alternatives exhaust the interior by symbolic coordinate bounds.

`kernel_exact_ten` subtracts the entire interior eight-ply region, using
weak-turn nine=eight. Thus both the winning region and the exact
distance-ten region have matching all-strategy lower bounds. Native
flags remain quantified; only coordinates are framed, and no incoming
history is transformed. This is a full interior board-geometry result,
not a complete ten-ply edge catalogue, next all-history clock band or
KRK closure. All results remain unfrozen.
