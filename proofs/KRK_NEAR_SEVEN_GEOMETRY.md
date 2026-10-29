# Evaluated near-corner seven-ply geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Work in the clock-free kernel with strong king K, strong rook R and weak
king W=(1,0). Coordinates run from 0 to 7. Assume distinct occupied squares,
king distance at least two, strong turn, and that R does not check W.
This result evaluates the seven-ply entry geometry; it does not evaluate
incoming-history barriers or complete the KRK class.

The six possible destination kings for a nonmating first move are
(0,2), (1,2), (2,2), (3,0), (3,1), (3,2).
For a king move to one of these points, require distance one, a destination
distinct from R, a safe rook after the move, and the following rook region:

| Destination king | Rook region after the move |
| --- | --- |
| (0,2) | x=2 and y>=2 |
| (1,2) | y>=3, or y=2 and x>=2, or y=1 and x in {2,3} |
| (2,2) | any square satisfying the stated distinctness and safety |
| (3,0) | y=1 and x>=3, or x=1 and y in {2,3} |
| (3,1), (3,2) | x=1 and y>=2, or (x,y)=(2,1) |

For a rook move, K must already equal one of those six points. The complete
condition on the **source** rook is:

| King | Source rook condition |
| --- | --- |
| (0,2) | x=2 or y>=2 |
| (1,2), (2,2) | always |
| (3,0) | x>=3 or 1<=y<=3 |
| (3,1) | y>=2 or (x,y)=(0,1) |
| (3,2) | y>=3, or y=2 and x<=2, or y=1 and x!=2 |

These conditions include actual line-of-sight blockers. In particular the
rook at (2,1) cannot count staying on that target as a move, and the strong
king at (3,1) or (3,2) blocks the horizontal approach from its far side.
Source distinctness is needed to remove spurious sources on the king square.

The proof reduces the already proved complete weak six-ply regions to the
six points, then solves vertical and horizontal line intersections. The
reverse direction constructs an ordinary legal rook move into a safe live
six-ply region. Immediate mate is included in the (1,2) rook-entry branch.
There is no position-value enumeration or engine/tablebase query.

`KRKSevenNear.kernel_seven_iff` proves that mate within seven is equivalent
to the union of these king and rook branches for every native position
meeting the assumptions, including its actual flags. `reach_iff`,
`king_points_iff`, `rook_rays_iff` and `clear_iff` expose the correspondence
to the existing global geometry. This work remains unfrozen.
