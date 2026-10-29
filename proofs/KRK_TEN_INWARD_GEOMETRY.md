# Complete ten-ply inward-corner geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For W=(1,1), distinct pieces, king separation at least two and weak
side to move, `KRKTenInner.kernel_ten_iff` proves the complete ten-ply
criterion. The canonical three king points below and their coordinate
transposes give all six destinations:

| K | R conditions |
| --- | --- |
| (3,0) | R=(x,2), x>=3 |
| (3,1) | The former eight-ply side region, or R rank 3, file at least 4, or file 3 with rank at least 2 |
| (3,2) | The former eight-ply high region, or R=(x,3), x>=3 |

The former side region is R=(x,2), x>=2, or R=(1,y), 3<=y<=4.
The former high region is R=(2,2), or R=(1,y), y>=3.
All definitions are explicit coordinate inequalities. No outcome table,
winning predicate or unevaluated minimax recurrence occurs in the criterion.

`kernel_exact_ten` subtracts the complete eight-ply inward-corner region,
using weak-turn nine=eight for the matching lower bound. `framed_clear_iff`
transports the criterion to every orientation through a coordinate frame,
while retaining actual native flags.

## Necessity

If (1,2) is a legal weak escape, the exact nine-ply near-strip criterion
must hold there. Its rook-entry alternative fixes K=(3,1) with precisely
the new side rook condition. Its king-entry alternative, combined with
the necessary covering of (2,2), forces K=(3,1) or K=(3,2); the latter
requires R=(x,3), x>=3. The transposed escape (2,1) gives the other
orientation.

If neither escape is legal, rook safety makes both squares covered;
(2,2) must also be covered because strong nine-ply forcing is impossible
at depth two. The existing exact corner-prison lemma leaves rank-2 rook,
file-1 rook and protected diagonal alternatives. The rank-2 families
reduce to the old eight-ply regions: a rook farther right than K=(3,2)
has its ray blocked by K and would make (1,2) legal after all.

In the file-1 side family K=(3,1), rook safety requires height at least
three. Heights at least five allow (0,2). After transposition this gives
K=(1,3), R=(x,1), x>=5 at W=(2,0); `KRKNineSecondLeft.no_nine`
excludes every strong entry there. King entries fail the central-edge
seven-ply condition after a legal weak reply; rook entries cannot produce
a live eight-ply position with that high left king. Hence only heights
three and four remain, exactly the former side region.

The protected diagonal prison K=(3,3), R=(2,2) permits (1,0).
`KRKNineNearDiagonal.no_nine` excludes every strong choice there. A king
entry that blocked the inward escape would land on its own rook; every
remaining entry fails the exact inward-corner seven-ply test. Rook
entries either leave the necessary inward square uncovered or produce
an unsafe adjacent rook. The diagonal prison is therefore excluded
without deleting the protected-rook resource from the rules model.

## Sufficiency

Old eight-ply families remain winning within ten by monotonicity. In the
new side family, the strong king covers the right three neighbours.
Every remaining legal edge reply admits a king entry to the diagonal
point (2,2) in an evaluated eight-ply corner, near-edge or second-edge
region. The latter uses the complete six-ply second-edge middle region
and monotonicity. Any legal (1,2) reply uses the exact nine-ply near-strip
rook-entry condition directly.

In the new high family, the same diagonal entries handle edge replies.
The rook's rank/file bounds give the second-edge middle-region tests in
both orientations. At (1,2), move K one step to the eight-ply near-strip
point (3,1). All destination certificates include distinct pieces, rook
safety and an actual weak reply. The explicit guard filters remain in
place when a rook attacks a potential weak destination.

`KRKEightDiagonalEntries` contains the shared live diagonal destination
proofs. They never infer forcing from a coordinate region that may be
stalemate. Claims and original incoming repetitions are not normalized;
this theorem evaluates board geometry only. The results remain unfrozen,
and lower-clock all-history/FIDE/global WDL-DTZ closure remains open.
