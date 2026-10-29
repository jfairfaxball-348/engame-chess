# Complete ten-ply near-strip geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For W=(1,2), distinct pieces, separated kings and weak side to move,
`KRKTenNearStrip.kernel_ten_iff` proves that forcing within ten plies
holds exactly in these five coordinate families:

| K | R |
| --- | --- |
| (3,1) | (x,3), x>=3 |
| (3,2) | (x,3), x>=2 |
| (3,2) | (1,4) or (1,5) |
| (0,4) | (2,y), y>=4 |
| (1,4) | (2,y), y>=3 |

The first family is exactly the previous eight-ply region. The remaining
four have exact distance ten: `kernel_exact_ten` subtracts that eight-ply
region, using weak-turn nine=eight to exclude every shorter strategy.
`framed_clear_iff` transports the complete criterion through any supplied
coordinate frame mapping W to (1,2). Native flags are never normalized.

## Necessity

Nine-ply strong forcing is impossible at depth at least two or on a
central first strip. Thus (1,3), (2,2), (2,3) must be covered. The
remaining neighbour (2,1) cannot be a legal escape either: the exact
nine-ply near-strip criterion after transposition would require rook
file 3, rook rank at least 3, and a king step to (1,3). King separation
then contradicts the covering requirement at (2,2). This proves the
stronger actual-guard exclusion `no_lower_guard`, retaining blockers.

The four covering constraints and rook safety give the same complete
prison families as at eight plies: king file 3 with rank 1/2 and rook
rank 3; king rank 4 with file at most 2 and rook file 2; king (3,2)
with rook file 1; or adjacent protected rook (2,3).

The rank-3 rook families give the first two table rows by safety. In the
file-1 rook family, the weak escape (0,3) and transposition give the exact
central-edge test `KRKNineMiddleLow.king_two_three_iff`: at W=(3,0),
K=(2,3), R=(x,1), nine-ply forcing requires x=4 or x=5. Its necessity
treats all strong moves: every eight-ply child has king rank two, and
the legal weak escape (4,0) then forces those two rook files. Its two
constructive entries establish sufficiency.

For a rank-4 king, rook safety and an inward-corner escape exclude rook
height zero. King file 2 is also excluded: height 3 yields the checked
boundary K=(4,2), R=(3,2), W=(2,0) after transposition; height 4 overlaps
the king; greater heights have the king blocking the rook's attack on
(2,1), making the forbidden lower escape legal. The boundary theorem
`KRKNineSecondBoundary.no_nine` proves failure against every strong
choice using covering constraints and the exact near-corner seven-ply
test, not a copied position value. The remaining king files 0/1 and rook
safety give the last two rows.

The protected rook (2,3) is retained throughout. Its safety and king
separation force king file 3 or rank 4. Rank/file alternatives outside
the table allow an inward-corner escape, contradicted by the complete
eight-ply inward-corner destination families. Both admitted protected
cases, K=(3,2) and K=(1,4), remain in the table.

## Sufficiency

The old family already forces within eight. For K=(3,2), R=(x,3),
the only legal weak replies are (0,1), (0,2), (1,1). The two edge
replies transpose to a king entry at (2,2) into evaluated eight-ply
near/second-edge regions. At (1,1), move the rook to (1,3) and use the
eight-ply inward-corner family.

For R=(1,4)/(1,5), the legal replies are (0,1), (0,2), (0,3).
The first two use diagonal/side king entries into eight-ply edge regions;
the last uses the exact central-edge rook-file-4/5 test above.

For the two upper families, the only legal replies are (0,1), (0,2),
(1,1). `KRKNineUpperEntries` constructs the edge continuations. The
near edge uses a king move to (3,1). The second edge uses a far rook
entry, a protected rank-1 rook entry, or a side king entry depending on
the king/rook coordinates. At (1,1), move K to (1,3) and apply the
vertical eight-ply inward-corner family. Each eight-ply destination
includes a legal defender reply, distinct pieces and safe rook; no
stalemate is passed off as forcing.

All arguments are symbolic coordinate/rook-line proofs checked in Lean.
The complete local build and public axiom audit pass using only propext,
Classical.choice and Quot.sound. This is a clock-free theorem, remains
unfrozen and does not evaluate the next global history/clock band. The
ten-ply inward-corner and edge catalogues, new castling audit, lower-clock
outcomes, FIDE correspondence and full WDL/DTZ remain outstanding.
