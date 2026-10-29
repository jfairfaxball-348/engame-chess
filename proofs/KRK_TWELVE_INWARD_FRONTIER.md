# Complete twelve-ply inward-corner geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

KRK remains open. This document records the complete twelve-ply board criterion for weak king (1,1). It does not extend the actual-history frontier below h=87.

## Complete diagonal family

For strong king (3,3), `KRKTwelveInnerDiagonalExact` proves that a weak-turn native KRK position wins within twelve plies exactly when the rook is (2,2), (3,2), or (2,3). Every such win has exact distance twelve.

For the necessary bound, inspect the upper near-strip reply (1,2). If it is blocked, the rook lies on file one or rank two. If it is legal, the complete strong eleven-ply near-strip criterion forces rank three or one of its file-one exceptions. Transpose this argument for reply (2,1). Safe-rook and distinct-material conditions reduce the intersection to the three displayed squares. This covers every possible strong entry through the prior iff theorem.

For sufficiency, the protected diagonal (2,2) has explicit king entries for all five edge escapes. For the two other rook squares, a king move to (2,2) enters the earlier eight-ply edge regions, hence the ten-ply regions. The one additional legal inward escape has an explicit entry into the ten-ply near-strip region. The entire earlier ten-ply inward criterion is false with strong king (3,3); weak-turn parity then rules out eleven.

## File-one extension

`KRKTwelveInnerFileOne` settles strong king (3,1), rook file one: the winning rook heights through twelve are exactly three, four, and five. Height five has exact distance twelve. Larger heights admit an edge escape excluded by the all-move eleven-ply edge bound. Heights three and four already belong to the earlier ten-ply region.

## Outer king family

`KRKTwelveInnerOuter` settles rook (2,3) and strong king (4,k), with 1 <= k <= 3. Exactly k=1 and k=2 win within twelve; both have exact distance twelve. The proof lists every legal weak destination and supplies an ordinary king entry for each.

For k=3, weak king can escape to (0,2). After transposition, strong king (3,4), rook (3,2), weak king (2,0) cannot win within eleven. A king move leaves a legal (2,1) reply outside the complete nine-ply near-strip criterion. A rook move must cover the central (3,1) reply; alignment then forces the rook to file three. Safe-rook excludes rank one, leaving the same nonwinning (2,1) reply. Thus both types of strong entry are excluded, rather than just the displayed strategies.

## Complete side and high families

`KRKTwelveInnerSide` completes all rook squares for strong king (3,1). The winning region consists of rank two with file at least two, file one with heights three through five, or the earlier nine-ply near-strip rook condition (rank three, file at least four, or file three with rank at least two). Its only exact-twelve addition is rook (1,5).

`KRKTwelveInnerHighExact` completes all rook squares for strong king (3,2). Its winning region is the union of:

- both rook coordinates at least two;
- file one, rank at least three;
- file zero, ranks three through five;
- file at least four, rank zero or one;
- the protected square (2,1).

Distinct material is retained, so the apparent king/rook collision at (3,2) is excluded. Necessity follows from safe-rook plus the complete eleven-ply criterion at the legal (1,2) reply; file-one and rank-two exceptions are handled separately. Sufficiency gives entries for every legal edge escape and for (1,2). The broad rectangle uses king (2,2) to enter earlier edge regions, with a separate protected (2,2) rook case. The (2,1) boundary uses an actual rook move to (2,3), and low rank-one rooks use a move to (4,1) when needed; no null rook move is admitted. Exact twelve subtracts the entire earlier ten-ply inward region, with weak-turn parity providing the all-move lower bound.

## Complete upper rank-four family

`KRKTwelveInnerUpperFour` settles all rook heights on file two for strong king (k,4), 0 <= k <= 2. For k=0 or k=1, precisely heights at least three win within twelve. For k=2, precisely rook (2,3) wins within twelve. All these wins have exact distance twelve. A rook above a same-file strong king leaves a legal deep (2,2) escape, so the own-king obstruction is included in necessity.

For the edge escapes, king (1,3) enters the proved ten-ply corner/near regions. On the left edge, transposition gives king (4,k); a king step to (3,1), or an actual rook move to (2,2), supplies the required entry. The near-strip reply has its evaluated eleven-ply entry. The separate upper-entry module proves and reuses these geometric regions without enumerating position outcomes.

## Complete upper rank-five family

`KRKTwelveInnerUpperFive` proves that, for strong king (k,5), 0 <= k <= 2, and rook file two, the only twelve-ply winner is king (1,5), rook (2,4). Its exact distance is twelve. Rook height three is excluded by the legal (0,2) escape: after transposition, every king entry leaves the near-strip reply outside the nine-ply region, while every rook entry that covers both inward replies leaves a capturable rook. King (2,5), rook (2,4) instead fails at escape (0,1); the complete king/rook entry analysis is in `KRKTwelveInnerUpperBoundary`. The remaining candidate has explicit entries for all five legal replies, including a real rook move from (4,2) to (4,1) in the transposed edge configurations.

## Complete inward and interior criteria

`KRKTwelveInnerExact.Horizontal` combines the low, side, high, diagonal, outer, rank-four and rank-five families above. `Region` is this union and its transpose. Necessity follows from the proved horizontal/transpose/corner-prison reduction. The residual corner-prison cases either enter the complete side/high/diagonal criteria or are the earlier low rank-two family. Sufficiency supplies actual entries, retaining distinct-material and far-king hypotheses. `kernel_twelve_iff` is the complete native board iff, `kernel_exact_twelve` subtracts the entire ten-ply inward region, and `framed_clear_iff` transports every inward corner.

`KRKTwelveInteriorExact` combines this result with the complete near strip, central strip and deep-second-corner criteria. It gives the twelve-ply iff and exact-twelve subtraction on every interior weak square. `KRKTwelveGlobal` adds the complete edge catalogue; see [the full-board criterion](KRK_GLOBAL_TWELVE_GEOMETRY.md).

## Remaining scope

The subsequent actual native-castling analysis and thirteen/fourteen-ply original-history band are proved; see [the history proof](KRK_THIRTEEN_FOURTEEN_PLY_HISTORY.md). Fourteen-ply first-strip/edge geometry, lower-clock/all-history closure, FIDE correspondence, terminal/capture coverage and global exact WDL/DTZ remain open. No result here is frozen or committed.

Verification: full local Lean build passed all 426 jobs; public axiom audit passed with only propext, Classical.choice and Quot.sound. No frozen records were changed.
