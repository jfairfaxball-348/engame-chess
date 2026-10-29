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

`KPK/Examples` contains small non-vacuity and move-boundary controls.
Outcomes in these controls instantiate the general theorems; they are
not computed class certificates. The axiom runner includes every new
public theorem. These sources are work in progress, **not frozen**.

Development verification on Lean `v4.35.0`:

- `lake build EndgameChess.Rules.KPK.Examples EndgameChess` passed
  (513 jobs in the incremental build graph, including cached dependencies).
- `lake env lean AxiomCheck.lean` passed. All 89 new public theorem
  reports use only subsets of `propext`, `Classical.choice`, `Quot.sound`.
- Local controls cover white/black promotion wins, double-push EP and
  path blocking, pawn capture draws, both turns of both edge-file corner
  fortresses, protected-corner stalemate and both minor promotions.

No clean-checkout certification or freeze has been performed.

## Open proof obligations

The remaining domain includes non-rook-pawn coordination, opposition and
tempo, blocked paths, and rook pawns outside the fortress. It needs a
complete explicit geometric win/hold partition, entry and preservation
lemmas, sufficient quiet-phase bounds, and prevention of fixed-height
king cycles. Height monotonicity alone settles none of those budgets.
General dead/live classification and the no-limit comparison needed for
cursed-win/blessed-loss labels remain open. No universal KPK winning
bound or class-completion claim is made.
