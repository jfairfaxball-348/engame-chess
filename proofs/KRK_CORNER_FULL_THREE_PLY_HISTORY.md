# Complete corner strong three-ply history formula

Status: locally Lean-checked, unfrozen. Exact RAW outcome for either strong
colour, not full KRK closure.

Assume ongoing admitted exact KRK, strong turn, W=(0,0), and halfmove clock
h>=96. The strong side wins exactly by immediate mate or a clear king point
or rook ray from the following two slots. All coordinates are zero-based.

| Slot | King K | Rook rectangle | Forced weak destination U |
|---|---|---|---|
| Horizontal | (1,2) | file>=3, rank>=1 | (1,0) |
| Vertical | (2,1) | file>=1, rank>=3 | (0,1) |

Immediate mate is exactly the disjunction:

* S.y=2, S.x<=1, R.x>=2, R.y!=0;
* S.x=2, S.y<=1, R.y>=2, R.x!=0.

For a **king point**, R lies in the slot's rectangle and dInf(S,K)=1.
Play S->K and then W->U. Require h<98 and fewer than two occurrences in
the original trace of each resulting position key.

For a **rook ray**, S=K. Choose either a vertical move R->(R.x,v) or a
horizontal move R->(v,R.y), with v a board coordinate. The destination
must lie in the slot's rectangle. A vertical move requires R.y!=v and
does not cross K when R.x=K.x. A horizontal move requires R.x!=v and
does not cross K when R.y=K.y. These are the strict-between coordinate
conditions in `Allowed`; no legal-move or future-outcome predicate
remains. W lies on neither permitted line and cannot block it.

For the actual rook move and W->U, require h<98 and fewer than two
occurrences of each resulting key in the original incoming trace. Thus
the full nonmating test has two king points and four bounded rook rays.
All keys are computed using actual `play`, retaining the incoming flags.

On the complement of this winning region, the weak side has a holding
policy against every strong alternative. Immediate-mate wins have exact
distance one. All other wins in this band have exact distance three.

## Proof correspondence

`last_slots_iff` evaluates the full corner LastReply formula as the two
rectangles and fixed king slots. `slot_reply_legal` constructs the actual
weak return. Every rook line has either its source file or its source
rank fixed (`line_target`), so the two-dimensional rectangle witness is
eliminated into the displayed rays. `ray_sees_iff` checks all blocking
conditions. Canonical move legality and unique-reply identification
then reduce KingHistoryEntry/RookHistoryEntry to the finite tests.

The complete three-ply history theorem supplies necessity against all
strong moves, including castling alternatives. The generic weak-prefix
identity can carry any such actual entry back through a first weak move
to the same original trace; it does not reflect that trace.

The source is `KRKCornerSlotBarriers.lean`, notably `KingPoints`,
`Allowed`, `RookRays`, `CornerClear`, `high_clock_force_iff`,
`high_clock_actual_iff`, `high_clock_hold_iff`, and
`high_clock_distance_cases`.

The transposed near-corner strong formula, W=(1,0)/(0,0) weak history
bands, other orientations and lower clocks still require completion.
Full FIDE correspondence and global WDL/DTZ semantics remain open.
