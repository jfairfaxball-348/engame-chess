# The last defender move in KRK

This working result evaluates the complete two-ply mating region with the lone
king to move. It is part of the positive-clock problem, not global KRK closure.
Coordinates below are zero-based. Write S for the strong king, R for the rook,
and W for the weak king. Kings are separated by Chebyshev distance at least two.

## Coordinate criterion

For a horizontal edge let W=(x,y), with either (y,S.y)=(0,2) or (7,5).
Require R.y≠y. The following table gives all alternatives:

| Weak king file | Strong king file | Rook file | Unique weak reply |
|---|---|---|---|
| x=0 | 1 | R.x≥3 | (1,y) |
| x=7 | 6 | R.x≤4 | (6,y) |
| 0<x<7 | x+1, or 6 when x=6 | x−1 | (x+1,y) |
| 0<x<7 | x−1, or 1 when x=1 | x+1 | (x−1,y) |

Include the transposed table for vertical edges. In either orientation require
**rook safety**: d∞(R,W)≥2 or d∞(S,R)=1. Call the resulting predicate LastReply.
This is an explicit coordinate predicate, not a recursive position-value table.

The rook-safety qualification is necessary. For example, White Ka3 Rc2 and
Black Kb1 satisfies the unqualified horizontal placement formula, but Black
can capture the rook on c2. A local diagnostic exposed this diagonal-capture
boundary; it is retained in the mathematical statement.

## Argument

The immediate-mate theorem gives all possible mating rook destinations. The
edge-predecessor lemma shows that a weak king moving into that region must
already have been on the same edge. With the strong king and rook fixed, at
most one neighbour of a legally separated weak king can be ready for immediate
mate. Thus every legal reply must be this same neighbour. The opposite edge
neighbour, when it exists, must be excluded by the rook's file; otherwise there
would be two distinct ready neighbours. The immediate-mate coordinate formula
then gives precisely the four rows above, including the corner offsets.

Conversely, each row admits its displayed reply. The strong king excludes the
inward moves, the rook excludes the opposite edge move, and board boundaries
exclude outward moves. Rook safety excludes captures. Every actual legal reply
therefore enters the immediate-mate region.

On exact weak-turn kernel boards the complete statement includes terminal
mate separately: MateWithin(2) iff MatedK or LastReply. Three plies have the
same criterion, since the final mating move must belong to the strong side.

## Incoming history

For an ongoing admitted history with the weak side to move, the two-ply
rule-aware certificate exists exactly when LastReply holds and the defender
has no current or intended-move claim in the existing RAW history layer.
The claim predicate uses the entire original trace. Its absence also ensures
that the intermediate strong-turn state remains below the clock and repetition
thresholds; immediate mate then takes precedence at the final state.

For halfmove clock h≥97, the exact deadline is at most three plies. Consequently
the same coordinate-and-claim criterion characterizes strong actual wins and
its complement characterizes weak holding in that layer. The winning cases
have exact optimal distance two board plies: no ongoing weak-turn root can
mate in zero or one ply. This does not assert
completed FIDE correspondence or classification at all lower clocks.

## Verification scope

Lean sources: `KRKLastReply.lean`, `KRKLastReplyKernel.lean`, and
`KRKLastReplyHistory.lean`. All three modules passed `lake build
EndgameChess.Rules.KRKLastReplyHistory`. Public results are included in
`formal/AxiomCheck.lean`. `scripts/krk_last_reply_diagnostic.py` passed 5,708
selected cases, including 164 positive cases. It is a reproducible boundary
diagnostic only, not proof evidence for untested positions.

The aggregate `lake build` passed (254 jobs). `lake env lean AxiomCheck.lean`
passed; the new public results use only `propext`, `Classical.choice`, and
`Quot.sound`.
