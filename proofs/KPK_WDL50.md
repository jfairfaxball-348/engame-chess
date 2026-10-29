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

`KPK/Examples` contains small non-vacuity and move-boundary controls.
Outcomes in these controls instantiate the general theorems; they are
not computed class certificates. The axiom runner includes every new
public theorem. These sources are work in progress, **not frozen**.

Development verification on Lean `v4.35.0`:

- `lake build EndgameChess.Rules.KPK.Examples EndgameChess` passed
  (524 jobs in the incremental build graph, including cached dependencies).
- `lake env lean AxiomCheck.lean` passed. All 168 public theorem reports
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

The remaining domain includes earlier-rank coordination, opposition when
the king-entry squares are guarded, blocked paths, and rook pawns outside
the proved fortress and support regions. It needs a
complete explicit geometric win/hold partition, entry and preservation
lemmas, sufficient quiet-phase bounds, and prevention of fixed-height
king cycles. Height monotonicity alone settles none of those budgets.
General dead/live classification and the no-limit comparison needed for
cursed-win/blessed-loss labels remain open outside the classified band.
No universal KPK winning
bound or class-completion claim is made.
