# Complete twelve-ply near-strip criterion

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

At weak king (1,2), `KRKTwelveNearExact.kernel_twelve_iff` proves the complete board region, with separated kings, both colours and native flags. The five coordinate groups are:

- K=(3,1), R=(x,3), x>=3 (the eight-ply family).
- K=(3,2), R=(x,3), x>=2 (the ten-ply row-three family).
- K=(3,2), R=(1,y), y=0 or y>=4.
- King rank four, rook file two: king file zero with rook rank>=4; king file one with rook rank>=3; or K=(2,4), R=(2,3).
- K=(1,4) or (2,4), R=(3,2).

`kernel_exact_twelve` eliminates all earlier regions and gives three explicit new families: K=(3,2), R=(1,y), y=0 or y>=6; K=(2,4), R=(2,3); and the two rank-two rook cases in the last group. These are necessary and sufficient exact-distance statements, not selected-policy upper bounds.

The lower diagonal reply (2,1) is retained because it can enter a genuine eleven-ply near-strip win. Three upper covered replies give the new prison. The complete four-point eleven-ply near-strip and six-point inward criteria then exclude king-rank-three row/file branches, the protected K=(3,4), R=(2,3) candidate, and the low upper rook R=(2,0). In the same-file upper case, a rook above K=(2,4) is blocked by its own king; the legal escape (2,2) excludes every rook rank>=5. The protected rook at (2,3) remains and has an explicit all-reply strategy.

The file-one family has exactly three left-edge replies, treated by actual rook/king entries. The rank-two rook family additionally retains its legal lower diagonal and inward replies. The finite fixed entries are established in `KRKTwelveNearFileEntries` and `KRKTwelveNearNewEntries`; the latter uses named earlier geometry and actual rays, including the null-move alternatives. No board outcome table or chess engine is used.

`framed_clear_iff` transports the entire criterion to all near-strip orientations. Original incoming-history barriers remain in the eleven/twelve-ply history certificates and may prevent a board win. Twelve-ply inward/edge closure and full KRK remain open.

Integrated local build: 408 jobs passed; public axiom audit passed with only propext, Classical.choice and Quot.sound. All work remains unfrozen and uncommitted.
