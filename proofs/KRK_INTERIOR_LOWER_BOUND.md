# Interior escape and a stronger KRK depth lower bound

For exact KRK with kings separated by at least two squares, let d>0 be the
weak king's Chebyshev distance from the nearest edge. The new necessary mate
budgets are

    strong to move: n >= 2d+5;
    weak to move:   n >= 2d+4.

These improve the previous [edge-depth bound](KRK_EDGE_DEPTH_LOWER_BOUND.md)
by two plies. They are lower bounds, without a matching global sufficiency
claim. All legal strong alternatives, including castling, and weak rook
captures are retained.

## Interior four-ply obstruction

The checked three-ply criterion requires the weak king to be on an edge.
Suppose a weak-turn interior root could force mate within four plies. The
rook must be safe, and every actual legal reply must enter that three-ply
region. Hence every neighbouring interior square must be covered by the
strong king or a rook line. A neighbouring rook square does not evade this
argument: safety means either it is too distant to capture or it is protected.

Reflect and transpose to the following coordinate cases. These operations
are justified through the existing same-budget strategy transport, applied
to temporary castling-free representatives. The three-ply necessity theorem
already covers all actual castling alternatives on the original boards.

* In the first inward file W.x=1 and 2<=W.y<=5, covering the five inward
  neighbours forces S=(3,W.y) and R.x=1. Safety forces |R.y-W.y|>=2. The legal
  reply (0,W.y) cannot enter the three-ply region: a king entry there requires
  R.y=W.y-1 or W.y+1, and a rook entry requires S.x=2.
* At W=(1,1), covering the three inward neighbours forces one of five families:
  S.x=3, S.y<=2, R.y=2; its transpose; S.x=3, S.y in {1,2}, R.x=1; its
  transpose; or S=(3,3), R=(2,2). Respectively, the replies (1,0), (0,1),
  (0,1), (1,0), and (0,0) are legal and outside the three-ply region.
* At distance at least two from every edge, all eight neighbouring squares
  remain interior. A separated king and a safe rook cannot cover all eight.

The last clause needs all eight neighbours. An earlier four-diagonal argument
was insufficient: for W=(3,3), S=(1,3), R=(4,0), all four diagonals are covered
while the middle neighbours on the third file remain available. The proof
uses the complete neighbourhood and does not rely on that failed shortcut.

Thus weak mate within four plies is impossible at every interior root.
Turn alternation also excludes a new mating opportunity on the fifth ply,
giving the first-band weak lower bound six. Every strong move preserves W
and reaches a weak-turn KRK state, giving the corresponding strong bound seven.

For larger depth, induct on the mate budget. A strong move leaves d unchanged;
a weak move changes d by at most one. Every weak node retains a nonempty set
of legal replies, and a winning weak node has a safe rook. The first-band
obstruction supplies the base; the two step relations propagate the displayed
2d+5 / 2d+4 lower bounds.

## Consequence for the same full incoming history

Combine the lower bound with the checked exact clock deadline. Any RAW forcing
win at a positive-depth admitted history must satisfy

    h + 2d + (5 on strong turns, 4 on weak turns) <= 100.

If the inequality fails, both players have RAW holding policies and the strong
side has no actual win. No freshness, incoming-key exclusion, or absence of
claims is assumed. The resulting explicit drawing regions are:

| Depth d | Strong-turn clock | Weak-turn clock |
|---|---|---|
| 1 | h>=94 | h>=95 |
| 2 | h>=92 | h>=93 |
| 3 | h>=90 | h>=91 |

These do not classify the remaining edge positions or earlier clocks, and do
not complete full FIDE/DTZ correspondence.

## Lean and diagnostic correspondence

`KRKFourPlyEscape.lean` proves the edge restriction, the strip and corner
covering families, and explicit escape replies. `KRKFourPlyInterior.lean`
proves transport, the full eight-neighbour obstruction, and the universal
coordinate contradiction. `KRKInteriorLowerBound.lean` lifts that contradiction
to the actual kernel, proves the five-ply exclusion, and gives the improved
depth induction. `KRKInteriorHolding.lean` supplies the full-history clock
inequality and both holding policies.

The focused build `lake build EndgameChess.Rules.KRKInteriorHolding` passed.
The aggregate `lake build` passed (261 jobs), and `lake env lean AxiomCheck.lean`
passed. The new public results use only `propext`, `Classical.choice`, and
`Quot.sound`.
The supplemental local diagnostic `python scripts/krk_four_ply_diagnostic.py`
checked 6,149 sampled/family roots, found 200 four-ply candidates, and found no
violation of the edge restriction on their replies. Its `--interior` mode
checked 10,230 selected roots with no four-ply candidate. These computations
helped discover the argument; the Lean proof establishes its universal scope.
