# KQK: general strategy proof

The owner selected full fresh-position WDL50, with a sufficient upper
bound under the 50-move rule. Exact mate distances are outside this work.
This document records the argument corresponding to the new Lean modules;
the complete fresh outcome is stated in [KQK fresh WDL50](KQK_FRESH_WDL50.md).
All results use the existing
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

## Entry by queen alignment and a checking staircase

`Setup.lean` proves entry into the copying strategy, rather than assuming
that its exact knight offset is already present. With the king's
coordinate sum at most 4 and the weak king's sum at least 8:

- If the queen is one or two files left of the weak king, both weak
  coordinates are at most 6, and the strong king is off the queen's file,
  a clear vertical slide reaches one of the two knight orientations.
  The upper bound, including the finish, is 53 plies.
- A two-file offset with a one-rank difference also has a 53-ply bound
  on the boundary. On the top rank it uses an edge wall; if that wall
  would have width one, it moves the queen left to widen it first.
- For the central input region `W_x,W_y ≤ 5`, `W_x+W_y ≥ 9`, a king
  blocking the queen's file can move one square left. The distant queen
  then prevents any weak reply from moving left. Each reply has sum
  at least 8 and coordinates at most 6, so vertical alignment applies.
  This proves a 55-ply bound without assuming the file is clear initially.
  The fresh-legality condition that the weak king is not in check supplies
  the required queen distance.
- From an arbitrary queen file, a clear horizontal slide to file
  `W_x-1` also gives a 55-ply bound, provided the queen's rank is at
  least two from the weak king's and the strong king lies strictly left
  of the destination file. Every subsequent weak reply enters the
  vertical alignment region. The horizontal clearance is an explicit
  geometric premise, not an assumed solution of the remaining blockers.

The file and blocked-file results transport through queen/king symmetry.
The examples include a king physically blocking the queen's initial
alignment file and a queen starting far to the right, so entry is not
vacuously the old shadow configuration.

`Staircase.lean` covers a farther queen with a one-rank difference. Its
region is

\[
K_x+K_y\le4,\quad Q_x+2\le W_x,\quad
|Q_y-W_y|=1,\quad Q_x+W_y\ge6.
\]

At a gap of at least three files, move the queen diagonally one step
to `(Q_x+1,W_y)`, giving a horizontal check from distance at least two.
Every legal reply leaves that rank and stays at least two files right
of the new queen. A vertical weak reply always exists; the coordinate
sum hypotheses keep it clear of the strong king. The inequality
`Q_x+W_y ≥ 6` is preserved because the queen advances one file and the
weak king changes rank by at most one. In particular, when the gap
reaches two, the weak king's coordinate sum is at least 8 and the
two-file entry theorem applies.

The nonnegative potential `7+W_x-2*Q_x` strictly decreases on every
defended pair: the queen's file increases by one while the weak king's
file can increase by at most one. Its initial value is at most 14.
Thus `2*potential+53 ≤ 81` plies suffice for this entire region and
its reflected/transposed versions. These are upper bounds sufficient
for the clock budget, not exact mate distances or a fresh-history
classification theorem.

## Edge corridor with unrestricted strong-king placement

`EdgeEntry.lean` removes the strong-king restriction from the edge-wall
input. `Corridor Q W` requires only

\[
Q_y=6,\quad W_y=7,\quad Q_x\le4,\quad Q_x+2\le W_x.
\]

For every exact strong-turn KQK board satisfying this corridor and
separated kings, `corridor_bound` proves mate within 41 plies. The king
may start on the queen's rank, on the last rank, or between the queen
and the weak king. The argument is general king evacuation:

1. Below rank 6, use the existing 25-ply edge strategy. On rank 6,
   step down to rank 5, opening the queen's horizontal ray. Every legal
   weak reply then remains in the corridor; cost at most 27 plies.
2. On rank 7 left of the weak king, walk left, away from it. The king's
   file strictly decreases, and every defended pair preserves the
   corridor. Once it is strictly left of the queen, it can step down
   without blocking the queen's ray. If both king and queen start on
   file zero, shift the protected queen to file one first. The resulting
   bound is `2*K_x+31 ≤ 41` plies.
3. On rank 7 right of the weak king, step diagonally down and away if
   room permits. At the right edge, a direct downward step suffices
   unless the weak king is at the left end of its corridor and the
   strong king guards its sole horizontal escape. The exceptional
   geometry forces queen file 3, weak file 5 and strong file 7.
   Move the queen left one file first; the weak reply moves left,
   giving room to evacuate the king. This branch costs at most 31 plies.

Each evacuation includes an explicit weak-reply witness and a proof
covering all legal replies. The proof never assumes that the defender
continues from stalemate. A local control example checks that the direct
downward king step in the exceptional geometry is legal but stalemates;
the general strategy avoids it. Reflection/transposition transports the
41-ply result to the other board edges.

The fixed-king reply lemmas still need their original king-rank/clearance
premises. This stronger entry theorem removes the *input* restriction
by moving the king first; it does not silently drop those premises.
Universal setup is proved separately below; the corridor result itself
does not supply that setup.

## General separating rank and monotone drive (Lean proved)

The new route in `BandGeometry`, `KnightPrison`, `RankFive`,
`BandProgress`, `BandRaise`, `BandForce`, `BandEntry`, `BandFrames` and
`ClearWallEntry` removes the absolute king-coordinate restriction of the
shadow argument. Coordinates remain zero-based. A strict upper-right wall is

\[
 K_y<Q_y<W_y,\qquad Q_x<W_x.
\]

For a strong-turn board whose weak king is not in check, **every such wall
forces mate within 91 plies**. `separating_rank_bound` also covers the weak
king to the left of the queen, by reflection. These are arbitrary exact
KQK boards with these geometric premises, not just the earlier low-king
families. The proof does not claim that every starting board already has
a separating wall.

First prepare the king at rank `Q_y-1` and file `Q_x`, keeping the queen
fixed. A weak move cannot cross either queen ray; the strong king remains
below the rank ray. In a prepared board maintain

\[
 K_y+1=Q_y\le5,\qquad Q_x\le K_x\le W_x,\qquad Q_x<W_x,
 \qquad Q_y<W_y.
\]

Use the natural-number potential

\[
 P(K,Q)=2(7-K_x)+2(7-Q_x)+4(5-Q_y).
\]

* If the king is at least two files behind, advance it one file. All weak
  replies leave it no farther right than the weak king. This defended pair
  decreases `P` by two.
* Otherwise, if the queen is at least two files behind the weak king,
  slide it to file `W_x-1`. The nearby king protects the target. Every weak
  reply stays to its right, and `P` decreases by at least two. The rank-five
  top-right corner is handled before a slide that would stalemate.
* Once the queen is exactly one file behind, a nonchecking strong-turn
  board has `W_y>=Q_y+2`. Below queen rank five, move the king diagonally
  up onto the weak king's old file. Every weak reply remains at least two
  ranks above the old queen rank. Then raise the queen one rank, protected
  by the king. This four-ply transition preserves the prepared conditions
  and decreases `P` by at least four.

Preparing the queen **exactly one** file behind before raising it matters:
with a two-file gap the intervening weak reply can move onto the new queen
file and escape to its other side. The formal strategy performs the file
preparation first; it does not assume this escape away.

Queen rank five and the rank-four right-edge transition have direct finishes
costing at most 33 plies. The top-right knight prison `Q=(5,5)`,
`W in {(6,7),(7,6)}`, with `K_y<=4`, finishes in 29 plies. A king tempo
selects the top-rank reply, then the queen widens the wall to `(4,6)`.
The narrow corner `Q=(6,5), W=(7,7)` is repaired by a queen check first.
The left boundary has a reflected-corner/two-reply fork repair. These
escape arguments are general geometric lemmas; they are not a computed
position catalogue.

The prepared bound is `P+33<=77`. Charge king preparation and this bound
together, rather than adding their independent maxima. The verified cost is

\[
 2\bigl(Q_y-1-K_y+|K_x-Q_x|\bigr)
 +4(7-Q_x)+4(5-Q_y)+33\le91.
\]

The exceptional rank-five corner and rank-six walls finish separately
inside the same 91-ply ceiling. Weak replies are explicitly nonempty in
every nonterminal recursive branch. The geometric escape witnesses cover
the whole band; no finite board enumeration is used in the proof.

`clear_wall_entry` additionally proves a 93-ply entry bound when the kings
have a rank gap of at least two, the queen's vertical slide is clear, and
the queen and weak king have a file gap of at least three. This margin
retains a reply even on queen rank six. This entry subfamily is a
component of the universal setup theorem below.

`FarFilePreparation` proves a first off-rank setup move without assuming
that a fixed far-file square is safe from stalemate. Orient the weak king
at file at least four, with a rank gap of at least two. If the queen is off
both kings' ranks and not already on file zero or one, choose one of those
two files. A horizontal weak escape at its current rank stays beyond the
strong king's reach; at most one of the two queen files sees it diagonally.
Choose the other. The queen is distant, an explicit weak reply exists,
and every legal reply retains the queen, leaves the weak king at file at
least three and at least one rank above the strong king, and keeps it off
the queen rank. This is a proved preparation transition; its remaining
blocked-file/one-rank-gap branches are composed in the subsequent entry
modules described below.

## Universal entry and fresh outcome (Lean proved)

`EntryGeometry`, `SetupCorners`, `EntryFrames`, `OrientedEntry`,
`TightEntry`, `FarFileEntry`, `SameRankEntry` and `StrongEntry` complete
the setup. Reflections/transposition normalise a king rank gap of at
least two. Off-rank queens use the escape-preserving far-file move above,
then vertical, horizontal or protected tight entry. The preparation costs
at most two plies and the complete far-file region at most 95, giving
97 plies. Same-rank queens use a backward king step, protected back-rank
entry, or an axis change; the same 97-ply ceiling covers every branch.
The narrow corner where the intended wall would stalemate has a direct
rook-pattern queen mate instead.

`strong_entry_bound` proves every strong-turn KQK board with the weak king
not in check wins within 97 plies. Every safe nonterminal weak turn wins
within 98, since all its legal replies retain the queen and enter that
theorem. `BoardOutcome` proves the forcing and dead/live criteria.

`FreshGame` starts at an arbitrary locally legal position, with clock zero
and an empty past. Actual future legal moves update clock and normalised
key occurrences, retaining current/intended draw claims. Decreasing
strategy rank makes every visited key distinct and every winning line
shorter than 100 plies. The finite rule certificates are equivalent to
independently defined actual bounded winning policies; holding uses
actual legal policies on every compliant prefix.

`KQK.fresh_wdl50` supplies the complete both-colour/both-turn result.
Exposed queens and stalemates have explicit holding arguments. Deadness
is a separate criterion; a drawn board need not be dead. See the companion
proof for the exact statement and scope. Certification/freeze provenance
is recorded in the theorem ledger, rather than inferred from this note.
