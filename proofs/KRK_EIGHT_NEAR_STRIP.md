# Exact eight-ply geometry next to an inward corner

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For weak king W=(1,2), distinct strong king and rook, and king distance
at least two, the complete nonterminal weak eight-ply criterion is

K=(3,1), R=(x,3), x>=3.

`KRKEightStrip.kernel_exact_eight` already constructs the win and proves
the matching exclusion at seven plies. `KRKEightNearStrip.kernel_eight_iff`
now proves necessity. Thus the former sufficient family is the entire
winning region on this weak square, with exact distance eight.

The inward neighbours (1,3), (2,1), (2,2), (2,3) are not inward corners.
Each must be covered by a king or rook line. Combining those four cover
constraints with king separation and rook safety gives four necessary
geometric cases (`Prison`):

* king file 3, rank 1 or 2, rook rank 3;
* king rank 4, file at most 2, rook file 2;
* king (3,2), rook file 1;
* protected rook on (2,3).

The fourth case is essential: this rook is adjacent to W but can be
protected by K. It cannot be discarded merely by requiring rook distance
at least two.

A king on rank 4 with rook file 2 permits the escape (0,1). Transposing
coordinates and applying the evaluated near-corner seven-ply criterion
would require rook rank 1 in the original coordinates, contradicting
its safety against W. For the file-1 rook case, escape (0,3) and the
central-edge seven-to-five reduction require a king rank inconsistent
with king file 3.

For king file 3 and rook rank 3, the escape (1,1) is legal. Its strong
seven-ply win must enter one of the two complete inward-corner six-ply
regions. The entry distances and rook coordinates force king rank 1;
rook safety then forces rook file at least 3. The protected-rook case
reduces to one of the excluded rank-4 or file-3 cases.

`framed_clear_iff` transports the resulting complete geometric criterion
through any supplied board frame mapping W to (1,2). The transport acts
on coordinates; native rights, histories and keys are not normalized.
The kernel theorem quantifies over actual native flags. Incoming-history
barriers still need evaluation for the full next clock band, and the
complete KRK class remains open. All results here remain unfrozen.
