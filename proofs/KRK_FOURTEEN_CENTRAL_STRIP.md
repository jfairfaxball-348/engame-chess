# Complete fourteen-ply central first-strip criterion

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

At weak king (1,3), `KRKFourteenCentralExact.kernel_fourteen_iff` proves a complete native board criterion for both colours, with far kings and distinct KRK material. Its region is the entire earlier twelve-ply central region together with:

- strong king (3,4), rook (r,2), r>=3;
- strong king (0,5), rook (2,h), h>=5;
- strong king (1,5), rook (2,h), h>=4;
- strong king (2,5), rook (2,4).

The height-four member of king (1,5) is already the twelve-ply protected family. `kernel_exact_fourteen` proves that all other additions displayed above, and only those, have exact distance fourteen. `framed_clear_iff` transports the criterion to every central first-strip square. Native flags remain in the board theorem; original-history barriers are separate.

The lower bound starts with the complete three-point thirteen-ply criterion in `KRKThirteenCentralStrip`. Its king points are (3,2), (3,3), (1,5), with evaluated rook regions and constructive ray conditions. The protected point has one rook destination, so its null rook move is explicitly excluded. The row-point necessity retains distinct material; a colliding king/rook source cannot be accepted as a legal ray.

At fourteen, the two deep noncorner neighbours must be covered. For a legal (1,4) reply, reflect and apply the three-point criterion; for a blocked reply, combine its covering condition with the two deep neighbours. `KRKFourteenCentralPrison` gives the resulting necessary families. `KRKFourteenCentralBounds` and `KRKFourteenCentralNecessary` exclude them through actual legal replies and all possible thirteen-ply entries, including the same-file rook-above-king obstruction. These necessity lemmas are not themselves asserted to be winning criteria.

For sufficiency, the opposition family leaves three legal destinations: (0,3), (0,4), (1,4). The edge entries reduce to the centered six-ply family and the inward reply to a proved central twelve-ply region. The upper families use explicit king/rook entries into twelve-ply edge and near-strip regions. `KRKFourteenCentralUpperZero`, `KRKFourteenCentralUpperEntries` and `KRKFourteenCentralUpperTwo` retain the protected boundary cases and supply all replies; no null rook move or copied position-value atlas is used. The exact lower bound subtracts the whole twelve-ply region and uses weak-turn thirteen-to-twelve parity.

Deep fourteen-ply geometry is complete separately in `KRKFourteenDeepExact`. The near strip, inward corners and edge remain open. The verified original RAW frontier is strong h>=86 and weak h>=85; full KRK, lower clocks, FIDE correspondence, terminal/capture coverage and global WDL/DTZ remain open. No freeze or commit has occurred.

Verification: full local Lean build passed all 453 jobs; public axiom audit passed with only propext, Classical.choice and Quot.sound. Frozen modules, manifests and ledger remain untouched.
