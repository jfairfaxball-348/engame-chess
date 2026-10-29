# Complete fourteen-ply deep-square geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For any native KRK weak-turn position with kings at distance at least two and weak king at depth at least two, `KRKFourteenDeepExact.kernel_fourteen_iff` gives a complete coordinate criterion. Only the four second corners (2,2), (2,5), (5,2), (5,5) can win within fourteen. Reflect the weak corner to (2,2). The winning region is the following union and its transpose:

- strong king (4,1), rook (r,3), r>=4 (the earlier twelve-ply family);
- strong king (4,2), rook (r,3), r>=3 (new exact-fourteen family).

`kernel_exact_fourteen` identifies precisely the second displayed family and its transpose, transported to each second corner. It excludes the entire twelve-ply deep region, with weak-turn parity ruling out thirteen.

The excluded central weak squares require coverage of seven deep noncorner neighbours, incompatible with far kings. For the eight remaining depth-two belt squares, `KRKFourteenDeepStrip.prison` reduces the possible king/rook arrangements to four necessary families. Each fails an explicit legal reply: either the second corner, or a first-strip square whose complete twelve-ply region excludes every thirteen-ply king/rook entry. `KRKFourteenDeepStripHolding` transports the result to all belt squares and proves the deep weak king must be a second corner.

At (2,2), three covered deep neighbours give the shifted corner-prison families. `KRKFourteenSecondCornerBounds` tests all strong king points and rook rays into the already proved twelve-ply regions at the critical replies. The own-king obstruction matters: a rank-three rook beyond a strong king on (4,3) does not attack the first-strip escape. The protected diagonal (4,4)/(3,3) also fails a legal inward reply; protection alone is not a win.

For the new winning family (4,2)/(r,3), r>=3, exactly three weak destinations remain: (1,1), (1,2), (2,1). The first two admit a king step to (3,2) into the twelve-ply inward/near regions. The third, after transposition, admits a rook step from (3,r) to (3,2), entering the twelve-ply row-two family with king (2,4). This includes the protected boundary rook r=3, and the rook move is non-null. The king (4,2) cannot belong to either twelve-ply second-corner king family, supplying the exact lower bound.

The central first strip is now complete separately in `KRKFourteenCentralExact`; the near strip, inward corners and edge of the fourteen-ply board remain open. Original-history outcomes are already proved for strong h>=86 and weak h>=85 using the explicit intermediate geometry; this geometric evaluation does not extend that clock band by itself. Full KRK, lower-clock histories, FIDE correspondence, terminal/capture coverage and global WDL/DTZ remain open. No result is frozen or committed.

Verification: full integrated Lean build passed 444 jobs; expanded public axiom audit passed with only propext, Classical.choice and Quot.sound. Frozen modules, manifests and ledger remain untouched.
