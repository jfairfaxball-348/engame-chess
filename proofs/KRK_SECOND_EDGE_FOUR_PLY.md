# Four-ply necessity and sufficiency at W=(2,0)

Status: locally Lean-checked, unfrozen. Exact KRK kernel geometry only.

For either strong colour, assume exact KRK, weak turn, king distance at
least two, and W=(2,0). Kernel mate within four plies holds exactly when:

* the root is already checkmate; or
* `LastReply(S,R,W)` holds; or
* S=(2,2) and R.y>=3.

This includes necessity against every legal strong-side continuation.
It is not restricted to a chosen rook strategy.

Necessity covers the three inward neighbours (1,1), (2,1), (3,1).
Every legal interior escape contradicts the checked three-ply edge bound.
The edge reply (1,0) is evaluated by the full near-corner formula, including
its additional king entry; (3,0) uses the middle formula. Their joint
constraints leave terminal mate, the last-reply region or direct opposition.
The rank-two source and diagonal rook-capture boundaries use piece
distinctness and safe-rook necessity explicitly.

For the added opposition family, every legal weak reply stays on rank zero
and reaches file one or three. Both resulting strong states satisfy the
appropriate complete three-ply formula. At least one such weak reply is
legal, so no stalemate is promoted to a win.

The source is `formal/EndgameChess/Rules/KRKFourPlySecond.lean`, especially
`second_four_necessary`, `opposition_replies`, and `weak_four_iff`.

The clock-free winning region matches the central-file region, but its
original-history test cannot be copied unchanged. After the reply to file
one, a source rook on file two also permits the king entry to (1,2), with
a different subsequent weak square and different repetition keys. The
central rook-ray-only history theorem therefore remains restricted to its
proved domain.
