# Complete twelve-ply central-strip criterion

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

At weak king (1,3), `KRKTwelveCentralExact.kernel_twelve_iff` proves the entire twelve-ply board winning region:

1. K=(3,2), R=(x,4), x >= 3.
2. K=(1,5), R=(2,4), with the adjacent rook protected by its king.
3. K=(3,3), rook file one, rook rank at most one or at least five.

Every winner has exact distance twelve (`kernel_exact_twelve`). The entire central strip has no ten-ply weak win; weak-turn parity excludes eleven. `framed_clear_iff` transports the complete criterion to the other central first-strip squares while retaining native positions in the kernel theorem.

The lower bound begins with four covered replies outside the eleven-ply weak-square domain. Rook safety and the evaluated four-point eleven-ply near-strip theorem reduce them to three candidate families. In the upper candidate family, weak edge escapes exclude king file zero and two, and exclude king file one unless the rook is exactly (2,4). `KRKElevenEdgeBoundary` checks all king/rook entries into the ten-ply edge regions, including the stalemate boundary and blocked rook lines. These are symbolic geometric arguments, not copied position values.

The row-four strategy has three legal weak replies: (0,2), (0,3), (1,2). Explicit king steps enter the ten-ply second/middle edge families, and the near-strip rook criterion handles the last reply. The protected upper strategy also has three replies; rook steps and four-point near-strip entries handle each. The opposition strategy has only (0,2), (0,3), (0,4), all treated by explicit rook/king entries into proved ten-ply edge regions. Nonemptiness and safe captures are retained throughout.

The supporting modules are `KRKTwelveCentralStrip`, `KRKTwelveCentralEntries`, `KRKElevenEdgeBoundary`, `KRKTwelveCentralUpperEntries`, `KRKTwelveCentralUpper`, and `KRKTwelveCentralOppositionEntries`. The earlier `Candidate` predicate remains a necessary reduction; the exact criterion is `KRKTwelveCentralExact.Region`.

Local integrated Lean build: 401 jobs passed; expanded public axiom audit passed with only propext, Classical.choice and Quot.sound. Original incoming-history barriers can still prevent a board win. Full KRK, lower-clock history closure, FIDE correspondence and exact global WDL/DTZ remain open. Nothing is frozen, source-pinned or committed.
