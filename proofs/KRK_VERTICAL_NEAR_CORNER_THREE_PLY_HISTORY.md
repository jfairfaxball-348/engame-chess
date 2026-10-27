# Complete vertical near-corner strong history formula

Status: locally Lean-checked, unfrozen. This is an exact RAW outcome for
either strong colour, not full KRK closure.

Assume ongoing admitted exact KRK, strong turn, W=(0,1), and halfmove
clock h>=96. The winning criterion is immediate mate or a clear king
point/rook interval in this table:

| Slot | King K | Rook rank r | Minimum rook file b | Forced weak destination U |
|---|---|---|---|---|
| North | (2,2) | 0 | 2 | (0,2) |
| South | (2,0) | 2 | 2 | (0,0) |
| Inner | (2,1) | 2 | 1 | (0,0) |

Immediate mate is exactly S=(2,1), R.x!=0, R.y>=3. Its exact winning
distance is one ply.

A king point requires R.y=r, R.x>=b and dInf(S,K)=1. Play the actual
canonical king move S->K, followed by W->U. Require h<98 and fewer
than two occurrences in the original incoming trace of each resulting key.

A rook interval requires S=K. Choose destination (v,r), v>=b. Either
R.y=r and R.x!=v, or R.y!=r and R.x=v. In the latter case, if R.x=2,
K.y must not lie strictly between R.y and r. These explicit coordinate
conditions include all blocking and source-square exclusions. For the
actual rook move and W->U, require the same h<98 and original two-key
barriers.

The criterion has three king points and three bounded file intervals.
Its complement gives a weak holding policy against every strong move.
When winning without immediate mate, the exact rule-game distance is
three plies; winning within two is impossible.

## Actual histories are not transposed

Only the pure LastReply geometry is transposed. `last_swap_iff` proves
its invariance by coordinate symmetry and rook safety. Actual king and
rook move legality is then constructed directly in the incoming position,
using its own flags. Every repetition query is `play` applied to that
same actual position. No RAW history, castling flag or repetition count
is reflected, swapped or assumed invariant.

`KRKVerticalNearSlotBarriers.lean` gives `KingPoints`, `AllowedFile`,
`RookStrips`, `NearClear`, `high_clock_force_iff`,
`high_clock_actual_iff`, `high_clock_hold_iff`, and
`high_clock_distance_cases`. The complete three-ply history theorem
supplies necessity against all strong alternatives.

Together with the horizontal near-corner and corner formulas, this supplies
the child-state evaluations needed for weak W=(1,0)/(0,0), h>=95. Their
root claims, all legal weak replies and original-prefix tests still need
combining. Lower clocks, other orientations, full FIDE correspondence and
global WDL/DTZ distances remain open.
