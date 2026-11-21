# KPK: proved foundations and geometric regions

This is a partial proof of fresh KPK WDL50. It does **not** give the
complete winning criterion or classify dead/live for the class. All
statements below have corresponding Lean declarations; no class result
is inferred from the examples. The arguments are elementary material,
geometry and strategy arguments, not a claim of new chess theory.

## Domain and notation

Squares have zero-based coordinates `(file, rank)`. Write `σ` for the pawn
owner, `s` for its king, `p` for its pawn, and `w` for the other king.
`IsKPK q σ s p w` says these are three distinct squares and the board
contains exactly those pieces. `FreshLegal` adds separated kings
`dInf(s,w) ≥ 2`, pawn rank between 1 and 6 inclusive, no castling rights,
no root EP marker, and no check on the side which just moved. It does not
assert reachability from the standard initial position. `FreshGame.fresh`
supplies clock zero and empty prior history.

Oriented height is `h_white(p)=rank(p)` and
`h_black(p)=7-rank(p)`. Thus an unpromoted pawn has height 1 through 6,
and promotion occurs at height 7. The strong/weak names refer to material,
not turn. `Hold` is an actual legal policy preventing opposing mate on
every compliant finite prefix. It includes terminal endpoints and draw
claims. Both players holding establishes draw; it does not establish
deadness. `Within σ n` is a sufficient forcing bound in plies, not DTM.

## Exact moves and progress

A pawn attacks exactly one rank forward and one file sideways. The only
enemy piece in KPK is a king, which cannot be captured. There is no enemy
pawn for EP. Consequently a legal strong-side pawn move has the same
file, an empty target, and is either one step forward or the initial
two-step push with a clear path. Reaching the last rank requires exactly
one of queen, rook, bishop or knight; other moves require no promotion.
With separated kings, these pseudo-legal pushes are legal: the unchanged
strong king can only be checked by the weak king, whose square is fixed.

Every other strong move is an ordinary king step onto an empty square;
there is no rook to enable castling. Every weak move is an ordinary king
step, either preserving the pawn or capturing it into KK. The shared
lone-king move results supply that complete weak partition. The new
constructive weak-step lemma additionally excludes the pawn's directional
attack on the target. These statements hold with arbitrary stored EP.

A push increases height by exactly one or two. Every KPK-to-KPK legal
step therefore preserves the pawn square or strictly increases its
height. A promoted piece cannot be mistaken for a pawn in this argument.
A promotion push must be the single step from height 6. Every pawn move
really resets the clock, and promotion clears the raw EP marker.
No legal EP event exists in KPK, so effective EP is absent. Equal
repetition keys imply equal pawn squares; different pawn heights exclude
equal keys. This does **not** rule out king cycles at a fixed height.

## There is no unpromoted KPK checkmate

With separated kings the strong king is not in check. If the weak king
is in check, the checking piece is the pawn. Take an on-board horizontal
neighbour and an on-board vertical neighbour of the weak king. A pawn
checking the king attacks neither orthogonal neighbour, and neither
neighbour is the pawn's square. Separation of the kings ensures that at
least one of these neighbours remains at Chebyshev distance at least two
from the strong king. This follows directly from the coordinate distance
inequalities. The constructive weak-step lemma gives a legal escape.
Hence neither turn can be checkmate in exact unpromoted KPK.

Stalemate is possible. The no-mate lemma is not a liveness theorem:
promotion can create a mating piece later.

## The pawn side always holds

Consider the region consisting of K+X versus K, with `X` any non-king
piece of the pawn owner's colour, separated kings and no castling rights,
together with dead positions. Every legal step preserves this region:
ordinary strong moves preserve material, pawn moves may promote to any
of the four non-king pieces, and weak capture enters dead KK. Legal
mover safety preserves king separation. Deadness is forward closed.

Within every nondead board of this region the strong king is attacked
only by the weak king, so cannot be mated. Dead boards cannot be mating
endpoints either. Induction on legal reachability proves that even
cooperative play cannot mate the strong king. Applying the existing
actual-policy semantics gives strong-side holding at every fresh legal
KPK root, and excludes a weak-side actual forced win.

If the weak side is to move and the pawn is adjacent and unprotected,
it can capture into dead KK. This is a weak holding policy. Combining it
with strong holding proves this whole family drawn, without asserting
that every such root is dead.

## Promotion boundary and budgets

All four legal promotion choices have exact successor material. The
frozen bishop/knight results prove those two successors dead. For queen
and rook, the frozen weak-turn criterion applies: the successor wins
exactly when it is already mate, or the promoted piece is safe and the
weak king has a legal reply. A safe promoted piece alone is insufficient
because stalemate must still be excluded. Each winning major-piece
successor has a proved 98-ply board bound. Prepending the actual promotion
gives a 99-ply board bound at the strong KPK root.

In particular, a safe **checking queen promotion** wins: if replies exist,
the 98-ply queen result applies; otherwise it is mate. The composite
99-ply bound lifts from a fresh root to an actual fresh-game winning
policy using the existing rank-descending lifting theorem. The promotion
successor is never replaced by a fictitious fresh state.

For longer KPK play, `promotion_continuation` handles the real stored
prefix. Its input history consists entirely of unpromoted KPK boards.
The promotion move resets the clock. No old pawn board has the same key
as a later winning promoted board, since keys retain the board and a
promoted continuation cannot regain a pawn. Among newly appended boards,
the existing strategy rank strictly decreases. Keeping the disjunction
“old pawn board or larger strategy rank” as a past invariant gives one
occurrence at every winning continuation state. All weak replies remain
included; both current and intended draw claims are excluded by the
clock bound and key separation. This lifts any supplied sub100 promoted
bound, including the queen/rook 98-ply bounds, with the actual prefix
retained. It does not prove that a KPK strategy reaches promotion in time.

## Rook-pawn fortress

Let `f` be an edge file, `c` its promotion corner, and suppose the pawn
has height 1 through 6. Define the three-square region for the weak king:

- height 7 and file distance at most one from `f`;
- or height 6 on file `f`.

The following is a holding region for **all** strong-king squares
compatible with king separation, and for either turn and colour.

If the weak king is off `c`, it can return to `c`. In this three-square
geometry, king separation at its old square implies that `c` is also
safe from the strong king. The pawn cannot attack its own file, and its
height is below promotion, so `c` is empty.

If the weak king is on `c` and the pawn is below height 6, the two
orthogonal neighbours of `c` are empty of the pawn and unattacked by it.
At least one is safe from the strong king by the distance inequalities.
Both neighbours lie in the three-square region. If the pawn is at
height 6, it is adjacent to the weak king. When unprotected it can be
captured into dead KK. When protected, the strong king and pawn together
exclude every escape: this is stalemate, by the no-mate lemma.

Strong king moves preserve this geometry whenever legal. Nonpromoting
pawn moves preserve the edge file and admissible height. If the pawn
promotes, the corner cannot contain the weak king. The weak king is then
the horizontal neighbour of the corner (the vertical neighbour would
coincide with the height-6 pawn). Separation implies the promoted piece
is unprotected at distance one, so the weak king can capture **any** of
the four promotion choices into KK.

The invariant therefore includes the KPK fortress, dead positions, and
weak-turn positions with a legal capture into a dead board. A new general
`FreshGame.hold_of_invariant` constructs the actual policy from these
preserving choices. Coupled with universal strong holding, this proves
draw throughout the fortress. In particular **every fresh rook-pawn
position with the defending king on the promotion corner is drawn**.
This does not assert draw for every rook-pawn position.

## Side-by-side king and pawn on the seventh rank

`SupportedSeventh σ s p` means `h(s)=h(p)=6` and their files differ by
one. This is a winning region for either turn and colour. The promotion
square is empty: it is protected by the strong king, so king separation
excludes the weak king there. The single promotion push is legal.

The resulting protected queen cannot stalemate the weak king. In the
white orientation, the queen is on rank 7, its supporting king on rank
6 and an adjacent file. If the weak king is on rank 7, the queen checks
along the rank, with no intervening strong king. Otherwise use three
local candidate neighbours: one rank lower (one rank higher at rank 0),
on the weak king's current file and its available adjacent files. The
king-separation inequalities and the adjacent-file support condition
exclude coverage of all these neighbours by king attacks and queen
lines. At least one neighbour is safe and off every queen ray, hence a
legal reply exists. These are symbolic coordinate inequalities over all
squares, not evaluated position cases. Black uses the already proved
queen rank reflection **after promotion**; pawn rules are checked
directly for both colours.

Thus promotion is either mate or a safe queen position with a legal
reply. The frozen queen theorem gives a 98-ply continuation and a
99-ply total from the strong turn. On the weak turn the pawn is
protected and every reply preserves the side-by-side configuration and
king separation. Replies exist: a king on its promotion edge can step
back along its file; lower kings have an escape from the same geometric
argument. The board bound is therefore 100 plies.

The weak-turn rule proof does not apply a strict sub100 lifting theorem
to that 100-ply total. At the fresh root neither current nor intended
claims exist. After the first weak reply, the actual clock is at most
one and the prefix has length one. The strong side then promotes and
really resets the clock, retaining both KPK prefix boards. The existing
promotion-history theorem gives the full 98-ply continuation. This
constructs the actual winning policy with the 100-ply total.

## King on the seventh, adjacent-file pawn on the sixth

`SeventhKing σ s p` means `h(s)=6`, `h(p)=5`, and file difference one.
The pawn is protected. Its single push produces the preceding supported
seventh-rank region. The destination is empty and protected by the
strong king, so no weak reply or initial occupancy is discarded.

For this whole band, define the explicit stalemate predicate

```
SixthCornerStalemate(σ,p,w) :=
  h(w)=7 AND (file(w)=0 OR file(w)=7) AND |file(p)-file(w)|=1.
```

On a weak turn, this predicate holds exactly when no legal move exists.
To see completeness, try stepping one rank backward on the weak king's
file (up from oriented height 0). King separation guarantees safety
from the strong king and prevents occupying the pawn. If the pawn
attacks that target, the weak king must be on height 7, one file outside
the pawn. It can then move outward along height 7 unless it is already
at the corner. In the corner case the pawn attacks the backward square
and the strong king covers the inward escapes. Capture of the pawn is
excluded by protection. The general no-KPK-mate theorem makes this
stalemate, and the absence of any move makes the root dead.

The closed winning criterion on **this band** is

```
SeventhKingWins(σ,q,p,w) :=
  turn(q)=σ OR NOT SixthCornerStalemate(σ,p,w).
```

It is equivalent to an actual fresh WDL50 win for the pawn owner. The
complement is a draw with actual holding policies for both sides, and
is exactly the dead subset. Board forced wins and fresh actual wins
coincide on this band, so it has no cursed-win/blessed-loss exceptions.
The universal strong-side holding theorem still excludes every weak win.

The bounds are 101 plies from the strong turn and 102 from the weak turn.
They compose the first pawn advance, at most one reply before promotion,
and the 98-ply promoted continuation. Each pawn move resets the clock.
The possibly longer pre-advance history is handled by a new invariant:
every old pawn has height below 6. After the advance to height 6 none of
those boards can repeat. After the next weak reply, the new same-height
past board has the opposite turn, so it cannot repeat either. All weak
current/intended claims are accounted for; the final promotion retains
the full KPK prefix. The 101/102 totals are sufficient bounds, not exact
distances or bounds on one reversible interval.

For example, White Kc7/Pb6 against Ka8 wins with White to move, but is
dead stalemate with Black to move. The statement and proof also cover
the reflected edge and both colours.

## Quiet king entry and the centered support square

The preceding band theorems extend to a fresh position which can enter
one of their winning weak-turn states by a legal king move. The entry
certificate is entirely geometric: an adjacent king target, distinct
from the pawn, separated from the weak king, and satisfying either the
supported-seventh condition or the winning sixth-pawn band condition.
The sixth-pawn entry explicitly excludes the outside-corner stalemate.
No outcome is inferred from absence of an entry certificate.

The resulting totals are 101 plies for entry into side-by-side seventh
support and 103 for entry into the sixth-pawn band. The first king move
is quiet. The proof retains its actual one-board history and clock at
most one; it does not replace the entered board by a fresh state. At
this weak turn neither current nor intended claims are possible. A move
changes the turn, so the immediately previous board cannot contribute
an occurrence hit. Even a return on the following move gives at most
two occurrences. The next strong pawn move supplies the actual reset,
after which the earlier phase-separation arguments apply.

One direct consequence covers a king on its sixth rank, on a file
adjacent to a sixth- or seventh-rank pawn: if its vertical seventh-rank
entry square is safe, and entry does not cause the stated stalemate,
the position wins with the pawn owner to move. This is a sufficient
entry region, not a classification of the guarded-entry complement.

Now put a **non-rook pawn** on its sixth rank and its own king directly
ahead on the seventh. Both adjacent-file flank squares on the seventh
rank exist. Choose the flank away from the defending king. King
separation implies this square is safe: when the weak king is near in
rank, it is at least two files from the centered king, and moving to
the opposite flank increases that file distance; otherwise rank
separation suffices. This enters the adjacent-file sixth-pawn band.
Its corner-stalemate condition cannot occur at this root, because a
corner king one file from the pawn would already be adjacent to the
centered strong king.

This centered position wins for either turn. On the weak turn the pawn
is protected and every reply preserves the centered configuration.
Replies always exist: step backward along the weak king's file (up
from oriented rank zero). If the pawn attacked that square, the weak
king would have been adjacent to the centered strong king, contradicting
separation. The pawn owner's next move chooses the safe flank.

The weak-turn route has **two quiet entry plies** before reaching the
adjacent-file band, so its proof also retains the exact two-move prefix.
Through the intended third move, turn alternation limits occurrences
to at most two. Both current and intended claims are excluded. Before
the next pawn move the clock is at most three, and the short history
cannot reach the automatic repetition threshold. The pawn advance then
separates old heights and resets the clock, as already proved. The
centered totals are 103 plies with the strong side to move and 104
with the weak side to move, with no optimal-distance claim.

Combining centered and adjacent support gives the whole explicit band

```
SixthPawnKeyBand(σ,s,p) :=
  h(s)=6 AND h(p)=5 AND 1<=file(p)<=6 AND |file(s)-file(p)|<=1.
```

On this three-square band, `SeventhKingWins` remains the complete fresh
WDL50 criterion and its complement is exactly the dead subset. The
outside-corner stalemate can occur only in the adjacent-file branch;
the centered branch always wins. Both players have actual holding
policies in the drawn branch, the weak side never wins, and board
forcing agrees with fresh actual winning. Thus there are no cursed-win
or blessed-loss exceptions in this band. This does not classify rook
pawns with a centered king, earlier ranks, or a guarded entry square.

## Coordinate game and strategy plans

`KPK/Coord` restates exact KPK as a game on natural-number coordinates:
oriented heights, with files reflected so that the pawn stands on files 0
to 3. `Coord/Bridge` proves that its king steps, pushes, captures and
promotion checks correspond to legal moves in the rules kernel.

A `Plan` is a hand-written strategy: a phase of at most 40 for each position
in its region. With the strong side to move, a king step spends one phase, or
a pawn move ends the phase. A weak reply exists, cannot capture the pawn, and
never raises the phase. `Coord/Forced` proves that any plan gives an actual
fresh-game win within 604 plies. The rank combines pawn height with phase, so
equal repetition keys have equal ranks and earlier boards cannot repeat. Each
pawn move resets the clock, and at most 82 quiet plies pass between resets.
Promotion uses the real prefix through the existing history theorems.

## The lone king's replies

Away from its last rank, the lone king has a quiet move unless capturing the
pawn is its only option (`weak_reply`). On the last rank the same holds when
the pawn is below height 5, or more than two files away.

## The rule of the square

Let `n` be the pushes the pawn needs, counting the first double step. Suppose
its own king is not ahead of it on its file. If the lone king is more than
`n` king steps from the promotion square with the strong side to move, or
more than `n+1` with the weak side to move and no capture available, the
pawn runs: each reply lowers the distance by at most one, and each push
lowers `n` by one.

Promoting to a rook then wins, except in one position. A promoted rook leaves
a reply or gives check unless it would stalemate a king on `a1` with the
pawn's king on `a3` or `b3` and the pawn on `b7`, in the reflected or colour
reversed versions too (`rook_reply`, `run_rook`). There the strong side first
plays one waiting king move up the board, then promotes. This is a sufficient
region, `fresh_runaway_strong` and `fresh_runaway_weak`, not a classification
of positions outside it.

## Key squares of bishop and centre pawns

Let the pawn stand on a bishop or central file, reflected so that it is on
file `c` with `2 ≤ c ≤ 3`, at height `d ≤ 5`. If the pawn owner's king is on
the pawn's file or an adjacent one, exactly two ranks ahead of the pawn, the
pawn owner wins with the move, and wins with the lone king to move provided
that king is not next to the pawn (`fresh_key_strong`, `fresh_key_weak`).

The strategy, `keyPlan`, keeps the king one to three ranks ahead. High on the
board the pawn simply advances: at height at least 3 a push from two ranks
ahead leaves a position that wins with either side to move. At heights 1 and
2 the king advances a rank if the lone king could otherwise step onto the
square opposite it, and the pawn moves otherwise. A pawn move while the lone
king already holds that square puts it in zugzwang. If the lone king guards
all the king's entry squares from the pawn's file, the king sidesteps to the
pawn's file and takes the opposition. A lone king next to the pawn is met by
a pawn move under the king's protection, or by a sidestep keeping protection,
and it then stays behind the pawn. The one line that needs the last rank is
king beside the pawn at height 5, opposed from the last rank, lone king to
move: it must step aside, the pawn advances, and if it reached the promotion
square it must leave again. Each king phase is bounded, so `Plan` applies.

Promoted rooks are used because a rook next to the supporting king always
gives check or leaves a step down the board (`r6_good`).

The knight file is deliberately excluded. Working the same line by hand with
the pawn on `b5` fails against a king using `a7` and `a8`, because of the
stalemate with `c7` and `b6`. So these key squares are not expected to carry
over unchanged. That is a candidate obstruction from analysis, not a proved
draw.

## Guards

`Guard` in `KPK/Coord/Hold` is the drawing counterpart of `Plan`. It gives
regions in which every strong king move and pawn move leads to a position the
lone king can answer inside the region, or where it captures the pawn or is
stalemated, and where any promotion can be captured at once. A fresh root in
a guard is an actual hold for the lone king and excludes forced mate at every
length (`fresh_guard_strong`, `fresh_guard_weak`).

`topGuard` in `KPK/Coord/TopGuard` is the first instance, for a non-rook pawn
on the seventh rank with the pawn owner to move. The lone king holds on the
promotion square if the strong king cannot step onto a square diagonally
behind the pawn: standing directly behind it stalemates, and any other move
gives up the pawn. It holds beside the pawn if the strong king cannot reach
the far side of the promotion square, since a king that only protects the
pawn lets it step onto the promotion square (`fresh_top_hold`).

`sixGuard` in `KPK/Coord/Sixth` adds a bishop or centre pawn on the sixth rank.
Inside the pawn's square the lone king holds in three ways. It stands opposite
a king beside the pawn. It reaches one of the two squares ahead of the pawn no
later than the strong king arrives beside or ahead of the pawn. Or it reaches
the pawn before the strong king can protect it. Each lone-king square has its
own chosen reply, proved for every strong-king square by inequalities
(`s5_king`, `s5_push`, `fresh_six_hold`). This is a holding region. Exactness of
its boundary needs the matching winning plan, which is not yet proved.

For a bishop or centre pawn on the seventh rank with the pawn owner to move the
boundary is exact. Every legal root outside `topGuard` is in `SevS` (`sev_cover`)
and wins (`fresh_seventh_win`): the pawn promotes, or the king first steps off the
promotion square, gets next to it, or evicts a blockading lone king from a square
diagonally behind the pawn.

The sixth rank is exact in the same sense. Outside `sixGuard` a bishop or centre
pawn wins with the pawn owner to move (`fresh_sixth_win`). The plan is short. With
the king beside or ahead the pawn advances or the king steps ahead. Outside the
pawn's square the pawn runs. Otherwise the lone king is two files out, or next to
the pawn's file, or on a blockade square. The last is a draw unless the king has
arrived. In the second the king steps beside the pawn on a side the lone king
cannot oppose. In the first the king heads for the square behind the pawn, from
which it can choose its side (`step5_cover`, `six_move`). Other ranks, the lone
king's turn on rank six, and knight and rook pawns remain unclassified.

## Fifth-rank guard

`fiveGuard` in `KPK/Coord/Five4` adds a bishop or centre pawn on the fifth rank to
`sixGuard`, with the pawn owner to move. A fresh root in it is an actual hold for the
lone king and excludes forced mate at every length (`fresh_five_hold`). The matching
winning plan below shows that its boundary is exact.

The region `S4` (`KPK/Coord/Five`) asks that the king is not on a key square (the three
squares ahead of the pawn on the sixth and seventh ranks), that the lone king is inside
the pawn's square, and one of five things.

- The king is beside the pawn and the lone king stands two ranks ahead of the pawn, on
  the pawn's file or opposite the king.
- `M4`, the race. The lone king is as close as the king to each of the four key squares
  beside the pawn's file (`Rc`), and from the pawn's file it can meet a king heading for
  the file two out (`Oc`). Distances allow for the king's route round the pawn (`KR`,
  `Thru`) and the lone king's route round the pawn's attacks (`WR`, `Cross`, `Hit`).
- `Op4`. The kings are opposed on a file at least two out, the lone king on the sixth
  rank and the king on the last rank, or three files out with the king on the fourth.
- `Pr4`. The lone king touches the pawn and the king cannot step next to it.
- `Rr4`. The lone king is two files out on the pawn's rank and the king is too far away
  on the other side.

King moves (`s4_king`). In the race the lone king's default reply is one step towards
the square two ahead of the pawn. That step keeps every race against any king step
(`race_keep`, `kr_step`, `wr_step`, `rc_step`, `m4_step`, `w4_main`). The other cases
each have a chosen reply.

- Directly ahead of the pawn it steps back to the pawn or opposes a king beside it
  (`w4_c6`, `w4_bes`).
- Two files out on the pawn's rank it steps beside the pawn (`w4_u4`, `w4_far`).
- If the default step is blocked (`w4_blocked`), then one of these holds. The lone king
  is in front of the pawn and takes it. It is next to the pawn's file on the seventh and
  steps in front of the pawn (`w4_t6_top`). It is two files out on the sixth with the
  king on the last rank and steps beside the pawn, which then falls (`w4_u5_top`). It is
  three files out, and steps inwards to oppose the king or to keep the race
  (`w4_w5`, `w4_w4`). In every other blocked position the race conditions show that the
  king could not have reached the blocking square (`ex_t7`, `ex_t4`, `ex_u6`, `ex_u7`,
  `ex_w6`, `ex_w7`).
- Opposed kings (`w4_op`). If the king steps inwards along the last rank the lone king
  opposes it again or steps beside the pawn. If it steps outwards the lone king follows
  it or returns to the race. If the king is below, the lone king steps to the seventh
  rank two files out (`w4_low`).

Pawn push (`s4_push`). If the lone king touches the new pawn square it takes the pawn,
because the king is neither beside the pawn nor on a key square and so does not protect
it. Otherwise it steps to a blockade square of the sixth-rank guard: one file inwards,
on the sixth or eighth rank. The race conditions give exactly what `S5` needs. With the
lone king two files out the king is not next to any key square (`arr1_u`); three files
out it is not within two (`arr2_w`).

The region's clauses were found with the scratch closure checker described below, and
several were adjusted from its failure lists. What is proved is that the region holds,
and, in the next section, that every position outside it wins.

## Fifth-rank winning plan

The fifth rank is exact for bishop and centre pawns. Outside `S4` the pawn owner wins
with the move (`fresh_fifth_win`). With the lone king to move, it holds if it can take
the pawn or step into the guard (`fresh_fifth_weak_hold`), and otherwise loses
(`fresh_fifth_weak_win`). A lone king is never stalemated with the pawn on the fifth
rank, so there is no third case.

`fivePlan` in `KPK/Coord/FivePlan` extends `sixPlan`. A push hands over to the
sixth-rank plan. Each position outside the guard has a phase `Ph4` of at most 12
(`five_cover`), and each phase has a move that lowers it whatever the reply (`mv4`).
Unlike the sixth rank, the phase depends on the lone king as well as the king.

- The pawn advances whenever every reply then leaves the sixth-rank guard (`PushOK`).
  This holds when the lone king is outside the pawn's square (`push_out`).
- King on a key square (`mv_key`, `mv_front`). From a seventh-rank key square the pawn
  advances. From a sixth-rank key square beside the pawn's file it advances unless the
  lone king can oppose on the last rank; then the king steps in front of the pawn, or
  to the seventh rank on the pawn's file. Directly in front of the pawn the king steps
  aside, to the seventh rank if the lone king stands next to the promotion square.
  These take at most two king steps.
- King beside the pawn outside the guard (`mv_beside4`). One of the two key squares
  ahead of it is not next to the lone king, and the king steps there.
- A race is won (`mv_race`). The king steps straight towards a key square that it
  reaches first, counting its way round the pawn. A lone-king step gains at most one
  (`wr_back`), so the race stays won, and a won race excludes every clause of the guard
  except the two in which the pawn falls (`won_out`). The walk is therefore proved with
  three safety conditions left open (`mv_walk`), which are then discharged.
  - If the lone king cannot touch the pawn next move, they hold at once (`mv_far4`).
  - One step from a sixth-rank key square the king goes there, which also protects the
    pawn (`mv_arrive5`). One step from a seventh-rank key square it goes there; outside
    the guard the lone king is then not touching the pawn (`mv_arrive6`).
  - From diagonally behind the pawn the king steps beside it (`mv_behind4`).
  - If the lone king is two files out next to the pawn's rank, the race is to the far
    side and the king ends within one of the squares protecting the pawn
    (`mv_close_u`, `box_not_pr`). If it is beside the pawn, the only king square
    outside the guard is one step from protecting the pawn (`mv_close_t`).
- No race won, inside the square (`rest_ph`). The king is then nearer to an outer file
  than the lone king is to the pawn's file (`rest_side`), and the lone king stands two
  or three files out on that side (`rest_file`). For each of its squares the level
  races leave only a few king squares (`rest_u`, `rest_w`). In most the pawn advances
  (`push_ku`, `push_kw`). In the others the king first steps one file inwards
  (`mv_r1` to `mv_r4`).

The classes and moves were found with the scratch checker and are proved here without
it. The stalemated lone king on the sixth rank is still not classified.

## Knight pawn

Seventh rank. `KPK/Coord/KnSeven` repeats the seventh-rank win for every non-rook pawn.
The earlier proof needed a bishop or centre pawn only because its side predicate names a
file two out, which a knight pawn lacks on one side. With the two-file predicate `Sd1`
the same argument gives `fresh_seventh_win_k` and `fresh_seventh_weak_win_k`. Together
with `fresh_top_hold`, which already covered knight pawns, the seventh rank is exact
for knight pawns.

There is one knight-pawn exception. With the pawn on `b7`, the lone king on `a1` and the
king on `a3` or `b3`, a promoted rook or queen stalemates (`Trap7`). The king first
steps one file towards the centre on its rank, the lone king must leave the corner, and
the pawn then promotes.

Sixth rank, holding side. `knSixGuard` in `KPK/Coord/KnSix` adds a knight pawn on the
sixth rank to the top guard, pawn owner to move (`fresh_kn_six_hold`). Its region `S5n`
is the bishop and centre region `S5` read on the knight file, plus two positions: the
lone king on `a8` with the king on `c6` or `d8`. In those a king step to `c7` or `c8`
stalemates, the advance is answered from `b8` or by taking the pawn, and any other king
step lets the lone king to `b7` (`wn_corner`). The reply lemmas of `Sixth` hold for
knight pawns as written and their file bound was relaxed in place. Only the two rook-
file squares needed new lemmas (`hl5`, `hl7`, `wl5`, `wl7`).

Sixth rank, winning side. `KPK/Coord/KnSixWin` repeats `SixWin`, `SixMove`, `SixCover`
and `SixMain` for every non-rook file, with the same king-only phase `Phi`, and
`knSixPlan` in `KPK/Coord/KnSixPlan` assembles the plan on top of `sevkPlan`. Outside
the guard the pawn owner wins with the move (`fresh_sixth_win_k`). With the lone king to
move it holds if it takes the pawn, is stalemated or steps into the guard
(`fresh_kn_six_weak_hold`), and otherwise loses (`fresh_sixth_weak_win_k`). So the
knight pawn's sixth rank is exact for both turns. The knight-file differences are
these.

- The side predicate allows a dummy file off the board on the short side
  (`Kn.Sd`, `Kn.sd_left`).
- The region `Kn.S5` includes the two corner draws, so the lemmas that leave the guard
  exclude them (`Kn.nd_beside`, `Kn.nd_close`).
- With the lone king on `a8`, a king on `c7` or `c8` stalemates. These are the only
  stalemates with a pawn on the sixth rank on any non-rook file, by a scratch count
  that is not a proof. The reply lemma and the step onto a key square carry that
  exception (`Kn.six_reply`, `Kn.w_key`). The plan never needs such a step: the king
  is then next to the lone king already, or the position is one of the corner draws.

Fifth rank. The fifth-rank modules `Race`, `Five` to `Five4` and `FiveWin` to
`FivePlan` were restated for every non-rook file (`1 ≤ c` in place of `2 ≤ c`), and the
same region `S4` and phases `Ph4` serve the knight pawn. `knFiveGuard` and `knFivePlan`
in `KPK/Coord/KnFive` sit on the knight sixth-rank guard and plan. So the knight pawn's
fifth rank is exact for both turns: `fresh_kn_five_hold` and `fresh_fifth_win_k` with the
pawn owner to move, `fresh_kn_five_weak_hold` and `fresh_fifth_weak_win_k` with the lone
king to move. The changes for the knight file were these.

- A pawn advance is tested against the knight-aware sixth-rank region (`PushOK` now
  uses `Kn.W5win`).
- Two key-square positions need a king step where a centre pawn would advance. With
  the king on `c7` and the lone king on `a8` the advance stalemates, so the king steps
  to `b6`. With the king on `c6` and the lone king on `a7` the advance allows the
  corner draw, so the king steps to `c7` first (`KnEx`, `mv_key`). The key-square
  phase therefore runs to three, and every later phase moved up by one.
- With the lone king beside the pawn the side argument needs no file two out
  (`Sd1`, `race_far_t`, `m4_side1`). On the knight file no outer-file race exists on
  the short side, which `rest_side` proves directly.
- Two lemmas that use the file two out on the short side keep `2 ≤ c` (`w4_far`,
  `m4_u4l`). Their cases cannot arise on the knight file.

The knight pawn below the fifth rank is open.

The stalemate case on the sixth rank for bishop and centre pawns is closed. `six_reply`
excluded one position (king `b6`, pawn `c6`, lone king `a8`), but there the lone king
has the legal step to `b8`. So with a bishop or centre pawn on the sixth rank the lone
king is never stalemated (`six_reply_all` in `KPK/Coord/SixStale`), and with the lone
king to move it holds exactly when it can take the pawn or step into the guard
(`sixth_weak_cases`, `fresh_sixth_weak_hold`, `fresh_sixth_weak_win'`).

## Fourth-rank guard

For every non-rook pawn on the fourth rank (height 3), with the pawn owner to move, the
fourth-rank region `S3` is the fifth-rank region `S4` moved down one rank. Write `B` for
the strong king's rank one higher, held at the last rank (`Lift`: `B = b + 1` for `b ≤ 6`,
`B = 7` for `b = 7`). Then `S3 a b c e f` says that the lone king is off the last rank and
`S4 a B c e (f + 1)` holds with the lifted kings apart. Away from the board's edge, kings
and pawn keep their geometry when everything moves up a rank. The proof has three parts.

- **King steps** (`s3_king` in `KPK/Coord/Four`). A king step lifts to a king step one rank
  up, and the proved fifth-rank closure `s4_king` gives the lone king's answer. Lowering
  that answer gives an answer here (`w3_of_w4`, `step_lift`). Two kinds of step touch the
  edge. A step between the last two ranks lifts to no move at all. With the king on the
  last rank the lone king can still answer (`s4_pass`): it takes the pawn, steps beside it,
  answers outer-file opposition from the file two out (`m4_w7`), or steps towards the
  square two ahead of the pawn. Its races only shorten when the king does not move
  (`rc_pass`). The other kind is a step onto the last rank next to a lone king on the sixth
  rank, which would touch it when lifted. The races then fix the king three or four files
  out (`e2_cases`), and the lone king steps in front of the pawn or one file towards it
  (`e2_reply`).
- **Push, king low or on the last rank** (`s3_push_low` in `KPK/Coord/Four`). After the push
  the lone king takes the pawn or steps straight up after it. With the king on the last
  rank, the lifted region is then the fifth-rank region itself. With the king on ranks one
  to five, lowering the king only lengthens each of its races (`kr_up`, `m4_down`). Two
  lifted clauses become explicit races (`m4_b3`, `m4_o2`).
- **Push, king on the sixth or seventh rank** (`KPK/Coord/Four2`, `Four3`). Lowering such a
  king keeps every race (`rc_lower`, `m4_lower`), with one exception (`HiEx`). In that case
  the lone king is in front of the pawn on the last rank and the king is two files out on
  the seventh, so the lone king steps down in front of the pawn. If the king stands two
  ranks above the lone king, the step up would touch it. The lone king then steps one file
  towards the pawn: beside the pawn, which it takes next (`s4_beside_far`), or two files
  out, where it wins the race (`m4_w6`, `m4_q5`, `m4_q6`). The races fix which of these
  cases occur (`push_blocked`).

`fourGuard` joins this region to the fifth-rank guards of all non-rook files. A fresh root
in it holds for the lone king, and no forced mate exists at any length:
`fresh_four_hold` with the pawn owner to move, and `fresh_four_weak_hold` with the lone
king to move when it takes the pawn or steps into `S3`.

This region is **not** exact. Moving down a rank makes the pawn's square one rank
longer, so a lone king four files from the pawn can still catch it. The region also
leaves out a lone king on the last rank, and some positions where the lifted kings would
touch. A one-step scratch check finds a strong move outside the region that keeps every
reply outside it for most roots, but not all, so the fourth-rank classification and its
winning plan are open. Closed guards combine by union, so enlarging the region later
keeps these proofs.

The full fourth-rank region `R3` (`KPK/Coord/Four4`) adds two parts to `S3`.

- **Opposition** (`Opp`). Here the kings stand on one file outside the pawn. Either it is
  one file out with the king on the last rank and the lone king two ranks below; or two
  files out with the lone king on the sixth rank and the king on the fourth or last rank;
  or three files out with the king on the third or fourth rank and the lone king two to
  four ranks above. These positions hold by keeping the opposition. Each shape has one
  answer per king step that works on every non-rook file (`opp_king`, `opp_push`). The
  case lemmas `opp_*` were written out mechanically from a hand-checked reply table. Lean
  proves each answer from the definitions.
- **Tempo positions** (`T3`). These are the three places where the lift misjudges a king by
  one move: the lone king on the last rank, the lone king four files from the pawn, and
  the king on the last rank. Such a position belongs to the region when every strong move
  can be answered by a step into `S3` or `Opp`. The owner approved this definition on
  2026-11-20, applied once and only on these named slices. Repeating it would be
  retrograde solving. Its closure is immediate (`r3_king`, `r3_push`).

`fourGuardR` joins `R3` to the fifth-rank guards, giving `fresh_four_hold_r` and
`fresh_four_weak_hold_r`. A one-step scratch check finds no root outside `R3` without a
strong move after which every reply stays outside.

**`R3` is not exact.** That one-step check cannot see draws held by a cycle. A first test
of a winning plan (walk the king to a key square two ranks ahead of the pawn, phase = its
distance) failed at about 50 roots. Among them are kings in direct opposition on the fifth
and seventh ranks, at most two files from the pawn, with the pawn owner to move. One
example is pawn `c4`, king `a5`, lone king `a7`: 1.Kb5 Kb7 2.c5 Kc7 3.c6 Kc8 4.Kb6 Kb8
5.c7+ Kc8 6.Kc6 is stalemate, and other tries give the lone king the opposition. Adding
24 such positions to `R3` keeps it closed in the scratch check, so these are draws
outside `R3` (not yet proved in Lean). Each further addition then exposes a new layer:
positions that hold only through the previous layer, for example a lone king on the last
rank with the king on the third rank. Closing layer after layer from the checker's lists
would be retrograde solving, so it was stopped. The exact fourth-rank boundary needs an
opposition (corresponding-squares) argument written by hand. The winning plan waits on
it.

### Fourth-rank opposition (owner's choice, 2026-11-20; proved in `KPK/Coord/Four5`)

The key squares of a fourth-rank pawn on `(c,3)` are `(c-1,5)`, `(c,5)` and `(c+1,5)`. The
lone king keeps the king off them by guarding them, that is, by standing next to them.
After each king move it must reach a square that guards every key square next to the
king. The square `(c,6)` guards all three, and it is the only such square that a king on
`(c,4)` does not touch. So the side that must leave a face-off on one file loses it: the
opposition. Two clauses follow.

- **Distant opposition** (`OPP`). The kings are on one file at most four files from the
  pawn, the lone king on rank 7 or 8 and the king on rank 5 or lower, with an odd number
  of squares between them. The pawn owner is to move. The lone king answers every king step
  by moving to the same file and restoring the parity between ranks 7 and 8. The king
  cannot enter rank 6 next to it, since every such square touches the lone king. If the
  king leaves the four-file window, the lone king instead steps one file towards the pawn,
  into `S3`. The push is always answered.
- **Guard square** (`GS`). The lone king is on `(c,6)` and the king is two files from the
  pawn on rank 4, 5 or 6. The king can never face it on its file.

In Lean the distant opposition is one general lemma (`opd_king`): mirror the file and
restore the rank parity, or step into `S3` when the king leaves the window (`opd_out`).
After a push the lone king steps towards the square two ahead of the pawn (`opd_push`;
`ocr_toward`, `ocl_toward`). The guard-square cases (`gsq_*`) were written out mechanically
from a hand-checked reply table, and Lean proves each answer from the definitions. With
`C4 = C3 ∨ Opd ∨ GSq` and the tempo slice `T4` answering into `C4`, the region `R4` gives
`fourGuardO`, `fresh_four_hold_o` and `fresh_four_weak_hold_o`.

### Fourth rank: the lone king on the last rank (proved in `KPK/Coord/Four6`)

`R4` still missed 33 roots in the scratch check, all with the lone king on the last rank.
They hold by corresponding squares, which `Ret` lists as 20 shapes relative to the pawn.

- One file beside the pawn, the lone king reaches the guard square `(c,6)` before a king on
  the third rank can take the opposition. This also holds against a king two files out on
  the fourth rank on the lone king's side.
- Against a king beside the pawn on its rank, the lone king waits on the pawn's file on the
  last rank. From there it reaches whichever guard square the king's next step needs.
- Three files out, the lone king runs back ahead of a king below it. Against a king three
  files out on the fourth rank it stays one file nearer the pawn.

These shapes were found from the checker's lists, and each was then checked against the
chess reason above. The case lemmas `ret_*` were written out from a reply table, and Lean
proves each answer from the definitions. The explicit part `C5 = C4 ∨ Ret` is closed by
itself. With the tempo slice `T5` over it, the region `R5` gives `fourGuard5`,
`fresh_four_hold5` and `fresh_four_weak_hold5`.

The scratch check finds no root outside `R5` where every strong move allows a reply into
`R5`. A first winning-plan test (walk the king to a key square, push once the push wins)
still fails at about 31 roots on the three files. Those inspected are wins in which the
king first takes the opposition, or first defends the pawn, so a phase measure that sees
both is needed. Whether `R5` is exact is not proved. The winning plan settles it.

Winning-plan design (scratch, one step deep, not yet in Lean). With the pawn owner to
move outside `R5`, the plan pushes when every reply to the push leaves the fifth-rank
guard, a position with phase 0. Otherwise it makes a king step after which every reply
stays outside `R5` with a smaller phase. The phase is the least of the following.

- **Race:** the king's distance to a key square it is strictly nearer than the lone king
  (plain king distance; obstacles are not needed).
- **Face-off:** the king can step onto the lone king's file at most four files from the
  pawn, `k` files out. Facing it two ranks below on rank 5 costs `2 + 2k`, two ranks below
  on rank 6 costs `1 + 2k`, and four ranks below on rank 4 (distant opposition) costs
  `3 + 2k`. Each face-off forces the lone king aside, and the king follows with a cheaper
  face-off or a race.
- **Otherwise:** `20 +` the king's distance to the nearest key square.

The scratch check finds no failure on the three files: every root outside `R5` has such a
step. Since the phase is at most 27 and falls with every pair of moves, this is the
evidence that `R5` is exact with the pawn owner to move. Of the 7,116 roots outside
`R5`, 5,982 push at once, 707 race, 83 face off and 344 walk. Earlier failures came from
two gaps. A king stepping aside to unblock a winning push was not counted as progress.
Distant face-offs, and face-offs from rank 6, were missing.

Lean needs every reply shown to be outside `R5`, because 134 roots inside `R5` also
match a race or face-off. That includes the tempo slice `T5`. A position leaves `T5` when
one strong move has no answer into `C5`. The plan's own next move gives that move, and
the fifth-rank results give the case where it is the push.

First Lean pieces (`KPK/Coord/FourWin`):
- `lost4_w4win` turns a lost fifth-rank position for the lone king into the fifth-rank
  plan's winning phase, using `five_cover`.
- `pushok3_not_r5` shows that a winning push puts a position outside `R5`.
- `step_not_r5` and `step_not_t5` show the same for a king step after which every reply
  avoids `R5`, or `C5` for the tempo slice.

**Race class, proved (`KPK/Coord/FourKey`).** The key squares of a pawn on `(c,3)` are
`(p,5)` for `p = c-1, c, c+1`. `Key3 m` says that the king is within `m` steps of one of
them, the lone king is not, and the pawn cannot fall first: the lone king is more than
`m` steps from the pawn, or the king stands next to it. In such a position the king keeps
the same key square and loses one step per move.

- Step towards the key square (`key_tw`). The race survives every reply, because the lone
  king gains at most one step. A guarding king leaves the pawn only from the rank in front
  of it, one or two steps from the key square, and then the lone king cannot come next to
  the pawn (`tw_leave`, `leave_m`, `leave_far`).
- If that step would land on the pawn, the king steps beside the pawn instead (`key_round`).
- If that step would let the lone king take the pawn, the king stands in front of the
  pawn, and it steps beside it (`key_def`). With the king beside the square in front of
  the pawn and the lone king below the sixth rank, the pawn advances and the lone king
  never reaches the fifth-rank guard (`bes_push`). On the key square itself the pawn
  advances at once (`key0_push`).

`fourKeyPlan` puts this class on top of the fifth-rank plan, and `fresh_four_key_win`
gives an actual win for every fresh root in it, pawn owner to move, every non-rook file.
The scratch check of this exact move rule found no failure on the three files, which
guided the statements; the Lean proofs do not use it. The class does not mention `R5`. It
is a positive description of wins, so its replies need no "outside `R5`" argument.

**Face-off class, proved (`KPK/Coord/FourFace`).** The king steps onto the lone king's
file at most four files from the pawn, two ranks below it: on the fifth rank against a lone
king on the seventh, or on the sixth rank against a lone king on the eighth. A face-off
`k` files out costs `2 + 2k` from the fifth rank and `1 + 2k` from the sixth (`FC`).
The lone king cannot step down, so it steps sideways or up (`facew_reply`).

- If it steps away from the pawn's file, the king wins the race to the nearest key square
  on its side, or to the square in front of the pawn when it is one file out on the fifth
  rank (`facew_right`, `facew_left`).
- If it steps towards the pawn's file or straight up, the king faces it again, nearer the
  pawn or one rank higher, at a lower cost.
- With the king in front of the pawn every reply loses a race (`facew_front`).

`fourFacePlan` puts this on the race class, and `fresh_four_face_win` gives the actual win.
Like the race class it needs no reference to `R5`. The distant face-off from the fourth
rank is not included: against a lone king on the last rank it meets the corresponding
squares of `Ret`.

Scratch design for the rest (one step deep, not in Lean). With these two positive classes,
557 roots outside `R5` remain on the three files, all wins in the one-step check. For them
the plan must carry "outside `R5`". In the walking moves 650 replies stay in the remainder
off the tempo slices, where outside `R5` means outside `C5`, and 220 land on a tempo slice,
where the next move of the plan must also be shown to avoid `C5`.

The plan cannot simply push from key squares: when the lone king attacks the pawn from
behind with the king far away, the pawn must run (about 720 scratch failures otherwise).
The open design point is the walking class, the roots with no race and no face-off. They
have no positive description other than lying outside `R5`. So the plan must carry
"outside `R5`" for each reply. Shown by geometry, that means "outside `C5`", plus the
plan's next move for roots in the tempo slice, by induction on the phase. The scratch
race and face-off patterns also match 134 roots inside `R5`. These are races in which the
pawn falls on the way, and distant face-offs against a lone king on the last rank, so
the Lean classes must exclude them.

The same lift does not carry over unchanged to lower ranks. A scratch check of the
twice-lifted region on the third rank fails at about ten top-edge king steps. On the
second rank it fails at the double step, which does not move with the board.

## Negative results and method notes

- Unstructured `omega` over a whole region does not work. A closure lemma with eight
  candidate replies timed out at 280 and 500 seconds, and a class cover ran for 45
  minutes with no verdict. Choosing each reply by hand made the same work take
  seconds. Replace implications by small explicit facts and `clear` what a goal does
  not need.
- A timed-out Lean run prints nothing. Check its return code. A silent timeout was
  once misread as a pass, and real errors were then found.
- Promoted rooks are simpler to prove than queens in stalemate arguments.
- Key squares do not carry over to the knight file unchanged. Candidate draws such as
  king `b6`, pawn `b5`, lone king `b8` with the pawn owner to move arise from a cycle,
  which a one-step closure check cannot see. They are not proved.
- `max` in distance statements makes `omega` slow. State distance as `Ch`, a bound
  by four inequalities.
- A first statement of the blocked-reply lemma was false, because it ignored that the
  lone king may capture the pawn. A corrected single statement did not finish. It is
  now proved as `w4_blocked`, split by the lone king's square with one small lemma each.
- An `omega` call given four race facts at once did not finish in ten minutes. Deriving
  one negative fact per key square first (`rc1_not`, `os_not`) and then clearing the
  race facts made the same lemma check in about a second.
- `WR` facts carry nested disjunctions. One apartness goal took 246 seconds with two of
  them in context, and 15 seconds once only their distance part (`.1`) was kept. A case
  derivation over all race facts did not finish. Splitting it into fixed file offsets of
  both kings before `omega` made it finish in under three minutes.
- A race lemma stated for a general `n` failed until the case "the lifted king also
  arrives within `n`" was handed to the lifted race itself (`rc_lower`).

## Status of the scratch finder

Region clauses for ranks 2 to 5 and the rook pawn were developed with a scratch
script, outside this repository. It checks one-step closure of hand-written regions
and solves nothing. No Lean proof depends on it, and it is not evidence of any
outcome. Several clauses were adjusted directly from its failure lists. For the fifth
rank both sides are now proved in Lean, the holding side with hand-chosen replies and
the winning side with hand-chosen moves. The owner allowed the script for discovery on
2026-11-12. It was used to confirm statements before proving them, to list cases, and
to test hand-written move rules one step deep. The lifted fourth-rank region was found
with it and then proved in Lean. The fourth-rank exact boundary, ranks 2 and 3 and the
rook pawn are unproved. See the open obligations below.

## Paper-to-Lean correspondence

All paths below are relative to `formal/EndgameChess/Rules/`.

| Argument | Principal modules/declarations |
|---|---|
| Domain, directional checks, move completeness | `KPK/Material`, `KPK/Moves`: `pawn_legal_iff`, `strong_cases`, `weak_move`; shared `LoneKing.weak_cases` |
| No unpromoted mate | `KPK/Geometry`: `escape_square`, `not_mated` |
| Height, clock and key facts | `KPK/Progress`: `push_height`, `kpk_step_progress`, `pawn_resets_clock`, `different_height_different_key` |
| Universal strong holding | `LoneKing/Closure`; `KPK/Holding`: `no_weak_reachable_mate`, `fresh_strong_hold`, `fresh_no_weak_actual_win` |
| Exposed pawn draw | `KPK/Holding`: `fresh_unsafe_draw` |
| All promotion alternatives | `KPK/Promotion`: `minor_promotion_dead`, `queen_successor_iff`, `rook_successor_iff`, `fresh_checking_queen_actual_win` |
| Actual prefix at promotion | `KPK/PromotionHistory`: `promotion_continuation`, `queen_prefix_continuation`, `rook_prefix_continuation` |
| Strategy invariant construction | `FreshGame/InvariantHolding`: `hold_of_invariant` |
| Seventh-rank boundary | `KPK/Corner`: `corner_protected_no_moves`, `fresh_corner_draw` |
| All-rank rook-pawn fortress | `KPK/RookPawn`: `fresh_rook_fortress_draw`, `fresh_rook_corner_draw` |
| Oriented coordinate interface | `KPK/Coordinates`: `dInf_oriented`, `pawn_sees_oriented`, `square_eq_oriented` |
| Seventh-rank side-by-side win | `KPK/SupportedPromotion`, `SupportedOutcome`: `fresh_supported_strong`, `fresh_supported_weak`, `fresh_supported_win` |
| Pawn-advance prefix separation | `KPK/SupportedPrefix`: `supported_weak_prefix_win`; `FreshGame/ShortPrefix` |
| Sixth-pawn king support and stalemate | `KPK/SeventhKing`: `seventh_king_advance`, `seventh_king_moves_iff` |
| Exact outcome/deadness of the seventh-king band | `KPK/SeventhKingOutcome`: `fresh_seventh_king_wdl50`, `seventh_king_force_iff_fresh` |
| One/two quiet entry plies with actual history | `FreshGame/ShortPrefix`: `one_ply_no_claim`, `two_ply_no_claim`; `KPK/EntryPrefix` |
| Safe king entry from outside the proved bands | `KPK/KingEntry`: `fresh_supported_king_entry`, `fresh_seventh_king_entry`, `fresh_sixth_rank_entry_win` |
| Centered seventh-rank support of a non-rook sixth pawn | `KPK/CenteredKing`: `centered_flank_entry`, `fresh_centered_strong`, `fresh_centered_weak`, `fresh_centered_win` |
| All three seventh-rank support squares | `KPK/KeySquares`: `fresh_key_band_wdl50`, `key_band_force_iff_fresh` |
| Coordinate game and bridge to the kernel | `KPK/Coord/Game`, `Bridge`, `Promo` |
| Any strategy plan gives an actual win | `KPK/Coord/Forced`: `Plan`, `fresh_cert_win`, `fresh_plan_strong`, `fresh_plan_weak` |
| Lone-king replies and the rook-promotion trap | `KPK/Coord/Replies`: `weak_reply`; `KPK/Coord/Runaway`: `rook_reply`, `run_rook` |
| Rule of the square | `KPK/Coord/Runaway`: `runPlan`, `fresh_runaway_strong`, `fresh_runaway_weak` |
| Key squares of bishop and centre pawns | `KPK/Coord/Key`: `keyPlan`, `key_reply`, `r6_good`, `fresh_key_strong`, `fresh_key_weak` |
| Any guard gives an actual hold | `KPK/Coord/Hold`: `Guard`, `draw_hold`, `draw_no_force`, `fresh_guard_strong`, `fresh_guard_weak` |
| Seventh-rank holding region | `KPK/Coord/TopGuard`: `topGuard`, `fresh_top_hold` |
| Sixth-rank holding region | `KPK/Coord/Sixth`: `sixGuard`, `s5_king`, `s5_push`, `fresh_six_hold` |
| Exact seventh-rank win, pawn owner to move | `KPK/Coord/SevenWin`: `sevPlan`, `sev_cover`, `fresh_seventh_win` |
| Exact sixth-rank win, pawn owner to move | `KPK/Coord/SixWin`, `SixMove`, `SixCover`, `SixMain`, `SixPlan`: `step5_cover`, `six_move`, `sixPlan`, `fresh_sixth_win` |
| Lone king to move on the sixth and seventh ranks | `KPK/Coord/SixPlan`: `fresh_sixth_weak_win`, `fresh_sixth_weak_hold`, `fresh_seventh_weak_win`, `fresh_seventh_weak_hold` |
| General king race, fifth rank | `KPK/Coord/Race`, `Five`, `Five2`: `race_keep`, `kr_step`, `wr_step`, `rc_step`, `m4_step`, `w4_main`, `w4_u4` |
| Fifth-rank guard, pawn owner to move | `KPK/Coord/Five3`, `Five4`: `s4_push`, `w4_blocked`, `w4_op`, `s4_king`, `fiveGuard`, `fresh_five_hold` |
| Fifth-rank win: push, key squares, beside | `KPK/Coord/FiveWin`: `push_out`, `mv_front`, `mv_key`, `mv_beside4` |
| Fifth-rank win: the race | `KPK/Coord/FiveRace`, `FiveClose`: `wr_back`, `won_out`, `mv_walk`, `mv_far4`, `mv_arrive5`, `mv_arrive6`, `mv_behind4`, `mv_close_u`, `mv_close_t`, `mv_race` |
| Fifth-rank win: no race won | `KPK/Coord/FiveRest`, `FivePlan`: `rest_side`, `rest_file`, `rest_u`, `rest_w`, `rest_ph`, `mv_rest` |
| Exact fifth rank, both turns | `KPK/Coord/FivePlan`: `five_cover`, `mv4`, `fivePlan`, `fresh_fifth_win`, `fresh_fifth_weak_win`, `fresh_fifth_weak_hold` |
| Seventh rank, every non-rook pawn | `KPK/Coord/KnSeven`: `sevk_strong`, `sevk_weak`, `sevk_cover`, `sevkPlan`, `fresh_seventh_win_k`, `fresh_seventh_weak_win_k` |
| Knight pawn, sixth-rank guard | `KPK/Coord/KnSix`: `hl5`, `hl7`, `wl5`, `wl7`, `wn_corner`, `s5n_king`, `s5n_push`, `knSixGuard`, `fresh_kn_six_hold` |
| Sixth rank win, every non-rook pawn | `KPK/Coord/KnSixWin`, `KnSixPlan`: `Kn.six_reply`, `Kn.w_key`, `Kn.step5_cover`, `Kn.six_move`, `knSixPlan`, `fresh_sixth_win_k`, `fresh_sixth_weak_win_k`, `fresh_kn_six_weak_hold` |
| Fifth rank, every non-rook pawn | `KPK/Coord/FiveWin` to `FivePlan` restated for `1 ≤ c`; `KPK/Coord/KnFive`: `knFiveGuard`, `fresh_kn_five_hold`, `fresh_kn_five_weak_hold`, `knFivePlan`, `fresh_fifth_win_k`, `fresh_fifth_weak_win_k` |
| No sixth-rank stalemate, bishop and centre pawns | `KPK/Coord/SixStale`: `six_reply_all`, `fresh_sixth_weak_win'`, `sixth_weak_cases` |
| Fourth-rank region, king steps | `KPK/Coord/Four`: `Lift`, `S3`, `W3`, `w3_of_w4`, `step_lift`, `s3_king_moved`, `rc_pass`, `m4_pass`, `s4_pass`, `e2_cases`, `e2_reply`, `s3_king` |
| Fourth-rank push | `KPK/Coord/Four`: `kr_up`, `m4_down`, `s3_push_low`; `KPK/Coord/Four2`: `rc_lower`, `oc_lower`; `KPK/Coord/Four3`: `m4_lower`, `push_blocked`, `s3_push_high`, `s3_push` |
| Fourth-rank guard, every non-rook pawn | `KPK/Coord/Four3`: `fourGuard`, `fresh_four_hold`, `fresh_four_weak_hold` |
| Full fourth-rank region | `KPK/Coord/Four4`: `Opp`, `C3`, `T3`, `R3`, `opp_king`, `opp_push`, `r3_king`, `r3_push`, `fourGuardR`, `fresh_four_hold_r`, `fresh_four_weak_hold_r` |
| Fourth-rank opposition region | `KPK/Coord/Four5`: `Opd`, `GSq`, `C4`, `T4`, `R4`, `opd_out`, `opd_king`, `opd_push`, `gsq_king`, `gsq_push`, `r4_king`, `r4_push`, `fourGuardO`, `fresh_four_hold_o`, `fresh_four_weak_hold_o` |
| Fourth-rank last-rank corresponding squares | `KPK/Coord/Four6`: `Ret`, `C5`, `T5`, `R5`, `ret_king`, `ret_push`, `r5_king`, `r5_push`, `fourGuard5`, `fresh_four_hold5`, `fresh_four_weak_hold5` |
| Fourth-rank winning side, basic facts | `KPK/Coord/FourWin`: `Lost4`, `PushOK3`, `lost4_w4win`, `pushok3_not_r5`, `step_not_r5`, `step_not_t5` |
| Fourth-rank race class | `KPK/Coord/FourKey`: `Key3`, `Bes3`, `bes_push`, `key0_push`, `key_tw`, `key_round`, `key_def`, `key_move`, `K3`, `k3_move`, `fourKeyPlan`, `fresh_four_key_win` |
| Fourth-rank face-off class | `KPK/Coord/FourFace`: `FC`, `Face`, `FaceW`, `face_step`, `facew_keep`, `facew_front`, `facew_right`, `facew_left`, `facew_reply`, `fourFacePlan`, `fresh_four_face_win` |

`KPK/Examples` contains small non-vacuity and move-boundary controls.
Outcomes in these controls instantiate the general theorems; they are
not computed class certificates. The axiom runner includes every new
public theorem. These sources are work in progress, **not frozen**.

Development verification on Lean `v4.35.0`:

- `lake build EndgameChess.Rules.KPK.Examples EndgameChess` passed
  (563 jobs in the incremental build graph, including cached dependencies).
- `lake env lean AxiomCheck.lean` passed. All 207 public theorem reports
  introduced for KPK use only subsets of `propext`, `Classical.choice`,
  `Quot.sound`.
- Local controls cover white/black promotion wins, double-push EP and
  path blocking, pawn capture draws, both turns of both edge-file corner
  fortresses, protected-corner stalemate and both minor promotions.
  Further controls cover both colours and turns of supported seventh-rank
  wins, the same-board win/stalemate tempo distinction, the reflected
  black stalemate, and the 102-ply weak-turn certificate using real resets.
  King-entry controls cover both colours, the seventh-pawn endpoint and
  exclusion of an entry that would stalemate. Centered-support controls
  cover both colours and turns, including the 104-ply two-quiet-entry route.

No clean-checkout certification or freeze has been performed.

## Open proof obligations

The fourth-rank region `R5` is proved to hold and passes the one-step exactness check.
The fourth-rank winning plan, which would prove it exact, is open; its race and face-off
classes are proved (`fresh_four_key_win`, `fresh_four_face_win`). The remaining domain includes king approach to the key squares, opposition
when the entry squares are guarded, knight pawns, blocked paths, and rook pawns outside
the proved fortress and support regions. It needs a
complete explicit geometric win/hold partition, entry and preservation
lemmas, sufficient quiet-phase bounds, and prevention of fixed-height
king cycles. Height monotonicity alone settles none of those budgets.
General dead/live classification and the no-limit comparison needed for
cursed-win/blessed-loss labels remain open outside the classified band.
No universal KPK winning
bound or class-completion claim is made.
