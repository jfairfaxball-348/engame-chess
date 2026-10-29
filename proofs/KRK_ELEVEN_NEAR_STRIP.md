# Four-point eleven-ply near-strip criterion

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

At weak king (1,2), the ten-ply weak region has four possible strong-king coordinates: (3,1), (3,2), (0,4), (1,4). `KRKElevenNearStrip.region_shape` proves this exact reduction, retaining the two rook-line alternatives at king (3,2).

The eleven-ply strong-turn criterion `Eleven` is a king step into one of these four points with its evaluated rook region, or a rook move from an already matching king point. The latter moves are eliminated to explicit `RookCondition` inequalities. `rook_line_necessary` uses both distinct-material hypotheses, including that the source rook is not the weak king; `rook_destination` constructs a destination for every admitted condition. Thus these are all-move matching conditions, not a selected sufficient policy.

`kernel_eleven_iff` quantifies both colours and native positions, with king separation and a nonchecking strong root. `kernel_exact_eleven` subtracts the entire nine-ply near-strip criterion; strong-turn parity makes ten equivalent to nine. `framed_clear_iff` transports the result without erasing native flags.

This is a local board criterion. Original-history barriers remain represented in the global eleven/twelve-ply history certificates. Full KRK is open; nothing here is frozen or committed.
