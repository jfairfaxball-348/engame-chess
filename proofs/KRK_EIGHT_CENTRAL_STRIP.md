# Eight-ply exclusion on the middle interior strips

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

At W=(1,y), y in {3,4}, every interior neighbour lies outside the four
inward corners. A weak eight-ply winning board must therefore cover every
such neighbour by its king or a rook line: an uncovered interior escape
would leave a strong seven-ply board outside its proved weak-square domain.

The existing five-neighbour strip argument forces K=(3,y) and rook file 1.
The weak reply (0,y) is legal. Transpose coordinates to place that reply on
the bottom edge. The strong king is then on rank 3 and the rook on rank 1.
At the two central edge files, strong seven-ply forcing equals five-ply
forcing. Its evaluated low-rook criterion requires king rank 2. This
contradiction excludes the reply, hence the original weak eight-ply win.

Coordinate symmetries prove the same exclusion on b4, b5, g4, g5, d2, e2,
d7 and e7. `KRKEightCentralStrip.middle_kernel_no_eight` quantifies over
all native weak-turn KRK positions with separated kings on these squares.

Every first move from a strong ten-ply win would leave a weak nine-ply
win, which by parity is an eight-ply win on the same weak square. Thus
`KRKEightCentralStripHolding.strong_no_ten` excludes that possibility too.
At strong clock h>=90, the proved RAW deadline is at most ten plies.
`high_clock_holding` consequently establishes both-player holding and no
actual strong win, for every admitted incoming history on those squares.
The theorem preserves native flags and claim semantics through the
deadline and holding interfaces. It does not assert an all-clock draw.

These are checked supporting results, still unfrozen. The complete
near-corner/edge eight-ply catalogue and the remaining class obligations
remain open.
