# Eliminating the last-move search in KRK

Working argument supporting the positive-clock/history classification. Use
the kernel and notation of [terminal geometry](KRK_MATE_GEOMETRY.md), with
strong colour sigma, distinct king/rook/king squares S,R,W, strong to move,
separated kings and W not already in check. Arbitrary kernel flags are retained.

## Every mating move is a rook move

The terminal geometry places the attacking king two lines inward from the
mating edge. An ordinary king move revealing rook check must start on that
edge and finish two lines inward, which is impossible in one king step.
Castling ends with K/R on g/f or c/d of the same home rank. A horizontal mate
would require the king two ranks inward; a vertical mate would require the
rook on file a or h. Neither is possible. This rules out both types of king
move using their actual resulting boards, rather than removing castling rights.
No other strong piece exists, so the move must come from the rook square.

## Two explicit candidate squares, with exact clearance tests

Define T_h=(R_x,W_y) and T_v=(W_x,R_y). Let H(S,T,W) be the horizontal
terminal formula. Let V be its coordinate transpose. Let Clear(R,T;S,W)
mean R and T are distinct and on one file/rank, with neither S nor W strictly
between them (the existing `RookSees R T S W`). Then define

    MateNow(S,R,W) =
      [H(S,T_h,W) and Clear(R,T_h;S,W)] or
      [V(S,T_v,W) and Clear(R,T_v;S,W)].

This is a fixed coordinate formula, with no game recurrence, move enumeration
or hidden existential strategy. The terminal formula itself ensures that the
destination is empty and different from both kings. Strong-king safety follows
from the unchanged king separation.

Necessity: the mating move is a rook move. If the final check is horizontal,
the old rook cannot already have been on W's rank: the terminal king position
is off that rank, so W would already have been checked. Hence the move is
vertical and its unique destination is T_h. The vertical case is the transpose.
Sufficiency: the indicated rook move is legal by the explicit clearance and
separation conditions, and the terminal equivalence proves mate.

The intended rule-aware application is to replace the unevaluated immediate
mate existential in the existing h>=98 strong-turn theorem by `MateNow`.
Incoming claims are not erased: the root must be ongoing and the strong side
may decline its optional claim. Mate at the child takes precedence. Earlier
plies still require matching defender lower bounds and incoming-key barriers.

## Formal correspondence

[KRKMatingMove.lean](../formal/EndgameChess/Rules/KRKMatingMove.lean) proves the
actual castling exclusion and `mating_source`, without changing flags.
[KRKImmediate.lean](../formal/EndgameChess/Rules/KRKImmediate.lean) defines
`MateNow` exactly as above and proves `immediate_iff` against actual legal
kernel moves, for either colour. The source board is explicitly nonchecking
for the weak king; the trace-rooted application discharges that condition
from the preceding actual legal move.
[KRKImmediateHistory.lean](../formal/EndgameChess/Rules/KRKImmediateHistory.lean)
proves `high_clock_actual_iff` for every ongoing admitted strong-turn KRK
history with h>=98, and `high_clock_hold_iff` for its complement. The latter
is a real defender holding-policy conclusion, not merely failure of one policy.
Terminal roots still use the existing terminal classification. This supplies
an evaluated high-clock result, not closure of lower clocks or FIDE correspondence.
