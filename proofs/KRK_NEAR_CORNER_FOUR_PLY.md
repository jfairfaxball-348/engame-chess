# Four-ply classification one file from the corner

Status: locally Lean-checked, unfrozen. This is exact KRK kernel geometry;
the additional original-history outcome conditions are still open.

Let the weak king be W=(1,0), using zero-based coordinates. Assume exact KRK,
weak turn and king distance at least two. Mate within four plies holds iff
the root is checkmate, or it has at least one legal reply and satisfies one
of these rows:

| Strong king S | Rook condition |
|---|---|
| (0,2) | R.x=2 and R.y>=2 |
| (1,2) | R.y>=3, or R.y=2 and R.x>=2, or R.y=1 and R.x is 2 or 3 |
| (2,2) | R.x=0 and R.y>=2, or R.x>=3 and R!=(3,1) |

Necessity first covers the inward squares (1,1) and (2,1). Any legal
interior reply contradicts the checked three-ply edge bound. Each of
(0,0), (2,0) and (0,1) is then either covered by the king/rook or belongs
to its complete three-ply region. The last square uses the transposed
near-corner region. Their joint coordinate conditions imply the table or
terminal mate. The proof divides the king files into zero, one, two,
three and at least four. In the outer case, both inward squares force a
rank-one rook; the two adjoining-edge requirements then contradict rook
safety or each other. Rook coordinates remain symbolic throughout.

For sufficiency, every legal weak move lands at (0,0), (2,0) or (0,1).
The corresponding corner, middle-edge or transposed near-corner formula
proves kernel mate within three further plies. Each table row implies a
safe rook. The legal-reply hypothesis is retained explicitly, and the
checkmate disjunct has its own proof.

`KRKFourPlyNearCorner.lean` proves `near_four_necessary` and
`near_four_replies`. `KRKFourPlyNearKernel.lean` proves `near_four_safe`
and the exact `weak_four_iff`. Both colours and every actual legal
strong continuation are included through the checked kernel transport
and three-ply equivalence. No symmetry of incoming RAW histories is assumed.

This result supplies the board geometry for the late-clock history band.
It does not evaluate the original-history barriers, certify full FIDE
correspondence, or establish global WDL/DTZ distances.
