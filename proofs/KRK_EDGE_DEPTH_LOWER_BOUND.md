# Necessary time from the weak king's distance to an edge

Working lower-bound argument for all legal strong alternatives, not an upper
bound for a selected policy. It is intended to combine with the exact
turn-dependent RAW deadline and the fixed incoming-key barriers.

Write d(W)=min(W_x,7-W_x,W_y,7-W_y). If d(W)>0, the necessary
clock-free mate budgets are

    strong to move: n >= 2*d(W)+3,
    weak to move:   n >= 2*d(W)+2.

These are necessary bounds, not claimed exact minimax values. Incoming
repetition restrictions can only obstruct a win further.

The key extra two plies come from terminal geometry. Immediately before the
last rook move, S is two lines inward and W is on the mating edge. A legal
weak-king step into that configuration cannot have started off that edge:
the off-edge predecessor would be adjacent to S. Corner offsets in the
terminal formula obey the same constraint. Therefore the final weak step
starts on the edge as well as ending there. Reaching the edge from depth d
takes at least d earlier weak moves. A strong-root line then needs d+1 weak
moves plus its final strong move; a weak-root line needs d+1 of each.

The formal route uses the finite mate certificate, preserving every defender
reply. The depth changes by at most one on a weak king move and is unchanged
on every strong move, including castling. Legal rook capture is incompatible
with a winning certificate and is handled by the existing capture-safety
theorem. Stalemate is never treated as an available continuation. This is not
an exhaustive search and does not assume the defender cooperates with a
chosen mating policy.

## Exact clock obstruction and formal scope

[KRKEdgeDepth.lean](../formal/EndgameChess/Rules/KRKEdgeDepth.lean) proves
`mate_depth_lower` symbolically for the kernel's finite mate certificates.
It makes no assumption about a particular wall policy or an optimal move.
[KRKEdgeDepthHistory.lean](../formal/EndgameChess/Rules/KRKEdgeDepthHistory.lean)
combines it with the existing exact necessary deadline, retaining the entire
incoming history. Winning from positive depth requires

    h + 2*d(W) + (3 if strong to move, else 2) <= 100.

When the left side exceeds 100, `clock_depth_holding` supplies holding policies
for both sides and excludes `ActualWin` for the rook side. In particular:

| Weak-king depth | Strong-turn drawing obstruction | Weak-turn drawing obstruction |
|---|---|---|
| 1 | h>=96 | h>=97 |
| 2 | h>=94 | h>=95 |
| 3 | h>=92 | h>=93 |

Equality at 100 is deliberately not excluded. Depth zero is outside this
bound; immediate mates must remain available even at high clocks. A failed
clock inequality is a proved drawing obstruction. A satisfied inequality is
not a winning criterion: king/rook geometry, defender choices and historical
barriers can still obstruct mate. No exact minimax-distance claim is made.
