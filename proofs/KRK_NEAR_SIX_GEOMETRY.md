# Near-corner six-ply geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. KRK remains open.

Let W=(1,0), K=(a,b), R=(x,y), with exact KRK material, weak turn,
and Chebyshev distance d(K,W)>=2. The exact clock-free criterion
is terminal mate, or rook safety, a nonempty legal-reply set, and this table:

| Strong king | Rook condition |
|---|---|
| (0,2) | x=2 and y>=2 |
| (1,2) | y>=3, or y=2 and x>=2, or y=1 and x in {2,3} |
| (2,2) | any rook, subject to safety and a legal reply |
| (3,0) | y=1 and x>=3, or x=1 and y in {2,3} |
| (3,1) | x=1 and y>=2, or R=(2,1) |
| (3,2) | x=1 and y>=2, or R=(2,1) |

The first two rows and part of the third are the previously checked four-ply
region. The exact distance-six part consists of:

* K=(2,2), with x in {1,2}, or R=(3,1);
* the final three rows of the table.

Rook safety and a legal reply remain required. All other table entries force
in at most four plies. These distances concern the clock-free kernel and do
not establish native-history or FIDE distances.

## Necessity

The complete strong five-ply region excludes interior weak squares.
Consequently (1,1) and (2,1) must be covered. The side reply (0,1), after
transposing coordinates, is either illegal or in the exact near five-ply
region. The right reply (2,0) is either illegal or in the exact middle
five-ply region. Their joint coordinate constraints, king separation,
distinct material squares and rook safety yield terminal mate, the table,
or the apparent families K=(3,1), y=1, x>=4, and K=(3,0), R=(2,1).

That apparent family is excluded by exact visibility: the strong king blocks
the rook's attack on (1,1). The weak move to (1,1) is legal and reaches the
interior, where strong five-ply forcing is impossible. A bare rook-line
coverage test would incorrectly retain this family.

For K=(3,0), R=(2,1), the legal reply to (0,0) cannot be answered by five-ply
forcing. In the complete corner-entry catalogue, the nominal king destination
(2,1) is occupied by the rook; the other king entries are either outside the
four-ply region or stalemated. No rook entry is reachable. This exception is
excluded by `no_capture_square_entry`, using the catalogue rather than a
diagnostic outcome value.

## Sufficiency

The old four-ply rows reuse their verified proof. In each added family all
legal replies are among (0,0), (0,1), and (2,0). The last two replies are
evaluated by the explicit near and middle five-ply formulas, retaining exact
rook visibility.

For the corner reply (0,0), `KRKFiveCornerEntries` supplies actual entries:

* With K=(2,2), every nonchecking exact-material board admits a rook move
  to a safe, live four-ply corner region. Split the rook file into 1, 2,
  and >=3; choose an explicit target on its file or rank. Targets are
  distinct from both kings and the source, and no king blocks the move.
* With K=(3,0), R=(x,1), x>=3, move the king to (2,1). Its new position
  blocks the rook's line to (0,1), preserving a legal defender reply.
* With K=(3,0), R=(1,2), move the king to (2,1); with R=(1,3), move
  the rook to (1,2).
* With K=(3,1) or (3,2) and x=1,y>=2, move the rook to (1,2), or if it
  is already there move the king to (2,2).
* With K=(3,1) or (3,2), R=(2,1), move the king to (2,2).

Each destination is in the checked four-ply corner catalogue and has a
specific legal weak reply. These liveness checks prevent stalemate from
being mistaken for a winning entry.

The exact-distance assertion subtracts the checked near-corner four-ply
criterion and uses the weak-turn five-to-four parity theorem.

Sources: `formal/EndgameChess/Rules/KRKSixNear.lean` and
`formal/EndgameChess/Rules/KRKFiveCornerEntries.lean`. The full near-corner
necessity, sufficiency and exact-distance equivalence pass the local Lean
4.35.0 checker. The integrated `lake build` passed (320 jobs), and
`lake env lean AxiomCheck.lean` passed. New public declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. No hosted CI result or freeze
is claimed.

Native incoming-history barriers, the next strong/weak clock bands, actual
FIDE correspondence and global WDL/DTZ remain open. No freeze is claimed.
