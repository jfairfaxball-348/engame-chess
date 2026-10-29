# KQK: strategy proof under development

The owner selected full fresh-position WDL50, with a sufficient upper
bound under the 50-move rule. Exact mate distances are outside this work.
This document records the argument corresponding to the new Lean modules;
it does not assert class completion. All current results use the existing
board legality kernel. No tablebase, engine or per-position computation
is used in their proofs.

## Shared material and capture boundary

`Rules/LoneKing/Material.lean` defines K+X versus K for an arbitrary piece
kind. Its king/check interface assumes X is not another king.
`Rules/LoneKing/Moves.lean` proves that every legal weak move is a one-square
king move, preserving KXK or capturing X into KK. These statements retain
arbitrary flags; the weak side has no rook with which to castle.

For distinct pieces, X is safe against immediate capture iff it is at
Chebyshev distance at least two from the lone king or protected by its
own king. The forward implication needed for forcing is formalised as
`force_weak_safe`: if neither safety condition holds, the lone king legally
captures X and reaches dead KK. The reverse safety statement is
`safe_reply`, which proves every legal reply retains X. These arguments
do not depend on X's movement, apart from excluding a king as the captured
piece in the capture construction.

## Queen geometry and confinement

`Rules/KQK/Basic.lean` specialises the material interface. `QueenSees`
means an orthogonal or diagonal ray with neither other piece strictly
between source and target. `queen_attacks` proves correspondence to the
kernel, including blockers. `safe_reply` gives every surviving weak
successor and its king/queen attack exclusions. `rank_reply` reuses the
frozen rook barrier argument: queen rays include rook rays, so a weak king
cannot cross a separating queen rank. It deliberately asserts no reply
existence and no forcing conclusion.

`Rules/KQK/Moves.lean` constructs legal queen moves, strong-king steps and
noncapturing weak-king steps from these geometric premises, retaining the
actual successor's material and turn. `Geometry.lean` proves that every
adjacent square lies on a clear queen ray. Consequently a protected queen
directly below a weak king on the top rank delivers checkmate: all neighbour
squares either hold the protected queen or lie on adjacent queen rays.

The same adjacency fact shows that a fresh legal strong-turn position
already has a distant queen: the weak king, which just moved, cannot be
in check. Thus the initial strong-turn entry proof needs no separate
rescue of an adjacent unprotected queen. Queen capture remains an
essential weak-turn boundary, and chosen future queen moves still need
their own safety arguments.

## Edge-wall strategy (proved local family)

`EdgeWall sk qs wk` means strong king rank at most 5, queen rank 6 and file
at most 4, and weak king rank 7 at least two files to the queen's right.
Coordinates are zero-based. The assertion is geometric and covers every
exact KQK board satisfying it, both colours, rather than a list of boards.

1. Every legal weak reply remains on rank 7 and at least two files right
   of the queen. Rank confinement excludes descent; the diagonal queen
   ray excludes the next file. There is always a reply: step right unless
   on file 7, in which case step to file 6. The corridor has width at
   least two, and the strong king is two ranks away.
2. With queen file 4, the weak king alternates between files 6 and 7.
   Walk the strong king toward `(6,5)`, changing each coordinate by at
   most one per move. The distance to that square decreases by one;
   the king stays below rank 6, so both weak escape squares remain legal.
   At arrival, slide the queen to the weak king's file on rank 6.
   It is protected and delivers the checkmate above. Cost at most
   `2*dInf sk (6,5)+1 ≤ 15` plies.
3. For a general edge wall, if the weak king is already on file 6 or 7,
   slide the queen to file 4 (if needed) and use step 2. Otherwise place
   the queen two files left of the weak king. If it already stands there,
   take a harmless king tempo below rank 6. The weak king's only reply
   is one file right, strictly decreasing `6 - weakKing.file`.
   This costs two plies per decrease, followed by at most 17 plies for
   the final corridor. Hence `2*(6 - weakKing.file)+17 ≤ 25` plies.

The corresponding main declarations are `corner_prison_bound`,
`edge_wall_bound` and `edge_wall_twenty_five`. These are upper bounds;
they make no claim of optimality or of complete KQK WDL50.

`Prison.lean` removes the lower-rank restriction on the strong king in
the two-square corner prison, assuming separated kings. If necessary,
move the strong king left and then down out of the prison before the
approach. The weak reply witnesses are maintained throughout; the
resulting upper bound is 21 plies. `Symmetry.lean` adds diagonal
preservation to the existing rook/king symmetry interface, proves strong
move completeness and transports any supplied forcing budget without
changing it. `FramedFinish.lean` applies the edge and prison arguments
after queen-preserving reflection or transposition. These transform
board strategies, not incoming histories or game keys.

`CaptureBoundary.lean` proves that the lone king never forces mate from
separated-king KQK with no castling rights, including lines in which the
queen is captured. Legal moves preserve KQK with separated kings or
enter dead KK; deadness persists. Thus an unsafe weak-turn queen gives
neither side a forced mate in the board game. The fresh WDL50 strategy
and classification bridge remain part of the outstanding obligation.

`Examples.lean` includes two local kernel checks: a genuine corner-prison
position satisfying the proved bound, and the stalemate illustration
from the plan. Neither is used as a replacement for the general argument.

## Queen copying phase (proved region)

`ShadowGeometry.lean`, `ShadowExit.lean` and `ShadowForce.lean` prove a
driving strategy beyond the edge finish. Its domain is explicit:

\[
K_x+K_y\le4,\quad W_x+W_y\ge8,\quad
Q_x+1=W_x,\quad Q_y+2=W_y,\quad W_x\le6.
\]

The king is outside the driven region and the queen a knight offset
southwest of the lone king. Each weak reply has nondecreasing file and
coordinate sum. Since the weak king must actually move, `2*W_x+W_y`
strictly increases. Thus `21-(2*W_x+W_y)` strictly decreases; initially it
is at most 12. The queen copies the step to restore the knight offset.
Both its legality and a nonempty weak reply set are proved at every
iteration. The outside-king hypothesis prevents blockers and collisions.

When a reply reaches file 7, stop copying before it creates stalemate.
The exit has queen file 5 and vertical offset one or three. A queen step
normally produces a vertical edge wall. At the top corner use a horizontal
prison or a wider vertical wall. The bottom exception passes through a
checking queen move and the reflected prison. All exit branches cost at
most 27 plies. Composition gives `2*potential+28 ≤ 52` plies on the weak
turn, or 53 on the strong turn after a harmless king tempo. These remain
region theorems; neither arbitrary king placement nor arbitrary queen
setup is assumed solved.

## Stalemate reduction (proved generally)

`InteriorEscape.lean` proves that a separated strong king and a queen
at distance at least two cannot cover all eight neighbours of an interior
square. The proof splits by which side the strong king lies on; the five
neighbours away from it cannot all lie on the queen's four lines. It is a
coordinate argument over the eight local directions, not a computed
classification of positions.

In a nonchecking weak-turn KQK position the queen cannot be adjacent to
the lone king, because every adjacent square is a clear queen ray.
The geometric escape therefore supplies an actual legal weak reply.
Consequently every KQK stalemate with separated kings lies on a board
edge. This reduces the repair problem to boundary geometry, but does not
supply the missing global entry strategy.

## Outstanding class obligation

Establish a general entry strategy from every fresh legal strong-turn KQK
position, accounting for all weak replies, legal setup and blockers, queen-only
stalemate traps and nearby kings. Prove its cost fits the class budget
when composed with the finish. Then complete weak-turn capture/stalemate
and dead/live partitions and connect the full forcing/holding arguments
to fresh WDL50. No incoming clock/history or exact-distance catalogue
is required.

Proof critique: the edge wall includes a genuine two-square escape
condition. Removing the width condition can cause stalemate; removing
the king-rank condition can remove the last legal reply or block a queen
ray. Neither the local strategy nor shared safety lemmas settle general
entry. The current modules have not been frozen as a completed class.
