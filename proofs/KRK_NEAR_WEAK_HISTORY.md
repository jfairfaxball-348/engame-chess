# Complete weak near-corner late-clock history classification

Status: locally Lean-checked, unfrozen. Exact RAW outcome and winning
distance for either strong colour throughout this band; KRK remains open.

Assume ongoing admitted exact KRK, weak turn, W=(1,0), and halfmove clock
h>=95. Use the actual incoming trace H and zero-based coordinates. Let
L=(0,0), E=(2,0), N=(0,1), D=(1,1), and Q=(2,1).

For any displayed destination T, its coordinate guard G(T) is:

    dInf(W,T)=1, T!=R, dInf(S,T)>=2,
    and R does not see T with the weak king moved to T.

With a safe rook these are exactly the actual weak moves. Safety means
dInf(R,W)>=2 or dInf(S,R)=1. The strong side wins iff all these tests pass:

1. The rook is safe, h<99, and the root has fewer than three occurrences.
2. Both inward guards G(D) and G(Q) are false.
3. For each available edge reply L, E or N, its resulting actual key has
   fewer than two occurrences in H and its corresponding original-trace
   point/interval test passes:

| Weak destination | Strong child formula |
|---|---|
| L=(0,0) | [Corner king points and four rook rays](KRK_CORNER_FULL_THREE_PLY_HISTORY.md) |
| E=(2,0) | Second-file formula below |
| N=(0,1) | [Vertical near-corner points/intervals](KRK_VERTICAL_NEAR_CORNER_THREE_PLY_HISTORY.md) |

Immediate-mate rows need no further barrier. For each nonmating entry,
require h<97 and fewer than two occurrences in H of the actual strong-entry
key and its actual following weak-return key. Each position is computed
by starting at the original position, playing W->T, then the displayed
slot moves. All flags update through actual play. There is no future
outcome or legal-move predicate in this finite coordinate/count test.

The complement has holding policies for both players. A win has exact
distance two in LastReply and exact distance four otherwise. The checked
near-corner LastReply formula is itself three coordinate rows, including
the protected rank-one case.

## Complete second-file strong child

For ongoing strong W=(2,0), h>=96, immediate mate is exactly S=(2,2),
R.y!=0 and absDiff(R.x,2)>=2. Otherwise the complete entry table is:

| Slot | King K | Rook file f | Minimum rook rank | Forced weak destination U |
|---|---|---|---|---|
| East | (3,2) | 1 | 2 | (3,0) |
| West | (1,2) | 3 | 2 | (1,0) |

A king point requires R.x=f, R.y>=2 and dInf(S,K)=1. A rook interval
requires S=K and destination (f,y), y>=2. A source on f may move vertically
to any different allowed rank. Otherwise y=R.y and, on rank two, K.x must
not lie strictly between R.x and f. Both entries use h<98 and two key
counts below two in the incoming strong trace. After a first weak move,
these become h<97 and the two counts in the original weak trace H.

`KRKSecondStrongSlots.lean` proves the entire strong second-file band,
including win/hold equivalence and exact one/three-ply distances. The
root combination does not apply the earlier distant-rook-only criterion
to rank-one or rank-two sources outside its domain.

## Necessity, admission and matching bounds

Every RAW win projects to a kernel win and forces rook safety. All actual
weak moves are therefore canonical noncapturing king steps. Their five
possible destinations are precisely L,E,N,D,Q. Current and intended root
claim tests give the clock/current-count/first-child-count conditions.

A legal D or Q produces an interior weak king at a strong-turn clock of
at least 96. Any win there would yield a three-ply geometric region with
the weak king on an edge, a contradiction. At each available edge square,
the complete strong slot formula is necessary against every strong move.
`KRKWeakPrefixEntry` measures both later keys in H, using the opposite
turn for the first and a changed weak king square for the second.

For sufficiency, the displayed tests exclude every root claim. Ongoing
status supplies an actual root reply, so no vacuous reply condition is
promoted to a win. Every surviving reply receives a three-ply RAW
certificate; the proof verifies its admission, ongoing status, clock and
repetition count. One four-ply certificate covers every root choice.
The exact weak-three equivalence and the nonterminal weak-one obstruction
give the two/four distance split. RAW win/hold duality and universal strong
holding give the draw criterion.

## Formal correspondence and remaining scope

`KRKNearWeakBand.lean` defines `NearClear` and proves
`high_clock_force_iff`, `high_clock_actual_iff`, `high_clock_hold_iff`,
`high_clock_draw_iff`, and `high_clock_distance_cases`.
`KRKSecondSlotPrefix.lean` and `KRKCornerSlotPrefix.lean` evaluate the
remaining child tests in the original trace.

Together with the earlier results, this evaluates ongoing weak h>=95 on
bottom-edge files zero through four, for both strong colours. The actual
reflected/rotated histories, lower clocks, strong h=94/95, full FIDE-rule
correspondence and global WDL/DTZ semantics still require completion.
