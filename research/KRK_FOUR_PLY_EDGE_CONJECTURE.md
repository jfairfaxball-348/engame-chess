# Four-ply edge regions — coordinate conjecture

**NORMALIZED BOARD CASES CHECKED; FULL HISTORY OUTCOMES OPEN.** The tables
below are now covered by Lean necessity/sufficiency proofs at W=(0,0), (1,0),
(2,0), (3,0), (4,0), with exact KRK and separated kings. General board
symmetry and original-history transport must remain distinct. The tables
do not by themselves settle the remaining history-dependent outcomes.

The x=2 board case is now proved in `KRKFourPlySecond.lean`; the x=3,4
board case is proved in
[the central four-ply theorem](../proofs/KRK_CENTRAL_EDGE_FOUR_PLY.md). The W=(1,0) case is also proved in
[the near-corner four-ply theorem](../proofs/KRK_NEAR_CORNER_FOUR_PLY.md).
The [corner four-ply theorem](../proofs/KRK_CORNER_FOUR_PLY.md) is checked too.
Reflected versions and remaining history-aware outcomes are still open. The supporting central three-ply witness elimination is also checked.

Assume exact KRK, kings separated by at least two squares, the weak king to
move, and a nonterminal root with at least one legal reply. Coordinates are
zero-based. Normalize W=(x,0) with 0<=x<=3 by reflections/transposition. The
table describes clock-free mate within four plies. Terminal mate and
stalemate must remain separate; some displayed placements can be stalemate
when the nonempty-reply hypothesis is dropped.

## Central edge: x=2 or 3 (also x=4 or 5 by reflection)

The checked criterion is

    LastReply(S,R,W) OR [S=(x,2) AND R.y>=3].

Thus the added family is direct opposition with a rook at least three ranks
inward. Safety and all relevant capture boundaries remain in LastReply.

## One file from the corner: W=(1,0)

The checked region is the following row disjunction:

| Strong king S | Rook condition |
|---|---|
| (0,2) | R.x=2 and R.y>=2 |
| (1,2) | R.y>=3, or R.y=2 and R.x>=2, or R.y=1 and R.x in {2,3} |
| (2,2) | R.x=0 and R.y>=2, or R.x>=3 and R!=(3,1) |

The exceptional excluded square (3,1) admits a defender reply outside the
three-ply region. The adjacent rank-one cases cannot be merged into an
unqualified rook-ray condition because safety and king protection change.

## Corner: W=(0,0)

The checked region is the following row disjunction:

| Strong king S | Rook condition |
|---|---|
| (0,2) | R.y>=2 or R.x=2 |
| (2,0) | R.x>=2 or R.y=2 |
| (1,2) | R.y>=1 |
| (2,1) | R.x>=1 |
| (2,2) | R.x,R.y>=3; or R.x=0,R.y>=2; or R.y=0,R.x>=2; or R=(1,2) or (2,1) |
| (s,3), 0<=s<=2 | R=(2,1) |
| (3,s), 0<=s<=2 | R=(1,2) |

## Proof route

The interior theorem implies that every legal reply must be an edge square.
On a central bottom edge, cover the three inward neighbours, retain both
edge replies unless a rook file excludes one, and apply the three-ply region.
An offset strong king and a rank-one rook wall cannot support every surviving
reply; direct opposition is the only added central family. A rank-two rook
shares the king's rank and blocks one required relocation, whereas ranks
three through seven permit both clear rook entries. The corner and near-corner
cases require explicit checks on both adjoining edges.

A checked supporting result is the [coordinate-only three-ply formula](../proofs/KRK_CENTRAL_EDGE_THREE_PLY.md)
on a central bottom edge, eliminating the landing-square witnesses in Three.
For 2<=x<=5, distinct S,R, W=(x,0), put F-=x-1 and F+=x+1. The proposed
expansion is the disjunction of:

1. S=(x,2), R.y!=0 and |R.x-x|>=2 (immediate mate).
2. R.y>=2, R.x=F-, and dInf(S,(F+,2))=1.
3. R.y>=2, R.x=F+, and dInf(S,(F-,2))=1.
4. S=(F+,2), and [R.x=F- or R.y>=3 or (R.y=2 and R.x<S.x)].
5. S=(F-,2), and [R.x=F+ or R.y>=3 or (R.y=2 and S.x<R.x)].

Rows 4/5 eliminate the rook destination: a source already on the required
file has a free vertical ray; otherwise a horizontal crossing must stay on
the same side of the strong king when it shares rank two. This supporting
formula has now passed a Lean proof in `KRKThreePlyMiddle.lean`; its separate
selected-family diagnostic passed 14,384 cases without mismatch. This advances
the supporting elimination argument, not the unproved full four-ply table.

## Executed diagnostic

`python scripts/krk_four_ply_diagnostic.py --edge-formula` compares the proposed
table with every local legal weak reply entering the independently defined
three-ply coordinate formula, for the four selected bottom-edge families
W=(0,0),(1,0),(2,0),(3,0). It queries no engine/tablebase and stores no
per-position values. This is a falsification aid, not universal proof or a
history-aware classification.

The executed edge-table diagnostic checked 14,452 selected roots, found 440
positive cases and no mismatch. The command
`python scripts/krk_four_ply_diagnostic.py --middle-three` checks the separate
central three-ply expansion against the previously defined geometric Three
predicate; it checked 14,384 roots without mismatch. Neither result is a
Lean proof or an evaluated incoming-history barrier criterion.

Incoming-key barriers remain to be attached only after the geometric table is
proved. Retain every actual weak branch, its current/intended claims, all
strong alternatives, and the complete original trace.
