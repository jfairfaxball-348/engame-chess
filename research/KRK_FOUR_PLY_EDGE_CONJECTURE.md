# Four-ply edge regions — coordinate conjecture

**UNPROVED.** This note records the next geometric target after the checked
[interior escape theorem](../proofs/KRK_INTERIOR_LOWER_BOUND.md). The tables
below passed local diagnostics. They have no Lean necessity/sufficiency proof
and do not settle any new history-dependent outcome.

Assume exact KRK, kings separated by at least two squares, the weak king to
move, and a nonterminal root with at least one legal reply. Coordinates are
zero-based. Normalize W=(x,0) with 0<=x<=3 by reflections/transposition. The
conjecture describes clock-free mate within four plies. Terminal mate and
stalemate must remain separate; some displayed placements can be stalemate
when the nonempty-reply hypothesis is dropped.

## Central edge: x=2 or 3 (also x=4 or 5 by reflection)

The proposed criterion is

    LastReply(S,R,W) OR [S=(x,2) AND R.y>=3].

Thus the added family is direct opposition with a rook at least three ranks
inward. Safety and all relevant capture boundaries remain in LastReply.

## One file from the corner: W=(1,0)

Exactly one of the following rows is proposed:

| Strong king S | Rook condition |
|---|---|
| (0,2) | R.x=2 and R.y>=2 |
| (1,2) | R.y>=3, or R.y=2 and R.x>=2, or R.y=1 and R.x in {2,3} |
| (2,2) | R.x=0 and R.y>=2, or R.x>=3 and R!=(3,1) |

The exceptional excluded square (3,1) admits a defender reply outside the
three-ply region. The adjacent rank-one cases cannot be merged into an
unqualified rook-ray condition because safety and king protection change.

## Corner: W=(0,0)

Exactly one of the following rows is proposed:

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

A useful next supporting result is a **coordinate-only three-ply formula**
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
formula is also unproved. Its separate selected-family diagnostic passed
14,384 cases without mismatch. Prove it before using it in the four-ply proof.

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
