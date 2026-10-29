# Actual castling is not an eight-ply weak winning entry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. KRK remains open.

`KRKCastleEight.castle_not_eight` proves: for every exact KRK kernel board,
both strong colours and either actual castling direction, a legal castling
move whose child is not already mate cannot have a weak-turn child from which
mate is forceable within eight plies. Castling rights are retained in the
actual hypotheses. This extends the earlier six-ply exclusion by a new proof.

## New interior restriction

The complete strong seven-ply point/ray formula implies that an interior weak
king must be at one of the four inward corners. At a six-ply interior
destination the king distance is exactly two. One preceding king move adds
at most one; a rook move keeps that distance. Thus any interior strong
seven-ply board has d(K,W)<=3 (`KRKSevenReach.interior_king_near`).

When K is on rank zero, an interior weak king that is seven-ply winning must
therefore be on rank one: the other inward-corner rank, six, is too far away.
Consequently all interior replies on ranks at least two must be covered by
the strong king or a rook line at an eight-ply weak root.

If K and R are on rank zero, with the rook on files 2 through 5, any weak king
off rank zero has an interior neighbouring square of rank 2 through 6 that
is not on the rook file. The king on rank zero cannot cover it. This is a
legal escape into a non-seven-ply board, so an eight-ply weak win must start
with the weak king on rank zero.

## The two castled formations

For K=(6,0), R=(5,0), king separation places W on files at most 4. Choose an
interior rank-one reply on files 1 through 4, adjusting the two corner-adjacent
cases by one file. It is legal and cannot satisfy both the inward-corner and
distance-three restrictions. Therefore this kingside formation has no
nonmating eight-ply weak win.

For K=(2,0), R=(3,0), any W other than (0,0) has file at least 4. An interior
rank-one reply on files 4 through 6 gives the same escape. Thus the queenside
formation could be eight-ply winning only with W=(0,0).

Reflecting only the geometric predicates proves the corresponding rank-seven
facts for Black. The actual `canCastle` cases then determine the new king and
rook squares. Kingside castling is excluded immediately. Queenside castling
would require the weak king on the old corner rook square, contradicting the
actual rook required there by `canCastle` and exact KRK material.

`winning_entry_not_castle` applies this to admitted RAW winning first moves
at strong h>=90. The exact child deadline gives at most nine plies; weak-turn
parity reduces it to eight. Mate is treated separately. No current history,
repetition key or castling flags are geometrically transformed.

## Central-edge simplification for seven plies

`KRKSevenMiddle.kernel_seven_five_iff` proves that when W is on either central
edge file, strong seven-ply forcing is exactly five-ply forcing. Every first
move retains W, and the already proved weak central six-to-four equivalence
shortens its child. The earlier explicit five-ply middle formula therefore
also evaluates seven plies on these files, including the low-rook test.

Sources: `KRKSevenReach.lean`, `KRKCastleEight.lean`, `KRKSevenMiddle.lean` in
`formal/EndgameChess/Rules/`. Public main declarations are included in
`formal/AxiomCheck.lean`. The Lean 4.35.0 integrated build passes (338 jobs),
and `lake env lean AxiomCheck.lean` passes. New public main declarations report
only `propext`, `Classical.choice`, and `Quot.sound`. No freeze or hosted CI
success is claimed.

The complete eight-ply destination catalogue, strong h=90/91 and weak h=89/90
native outcomes, lower clocks, FIDE correspondence and global WDL/DTZ remain
open. The central-edge simplification is a clock-free statement; it does not
erase or simplify native-history barriers by itself.
