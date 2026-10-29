# Eight-ply inward-corner geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For weak king W=(1,1), distinct strong king K and rook R, and king
separation at least two, `KRKEightInner.kernel_eight_iff` characterises
clock-free weak-turn forcing within eight plies by the following regions
and their coordinate transposes:

| K | R |
| --- | --- |
| (3,0) | (x,2), x >= 3 |
| (3,1) | (x,2), x >= 2 |
| (3,1) | (1,y), 3 <= y <= 4 |
| (3,2) | (2,2) |
| (3,2) | (1,y), y >= 3 |

These are board-kernel statements with actual native flags. They do not
yet evaluate incoming-history barriers or assert the full KRK outcome.

For necessity, every neighbouring interior square must be covered: none
is another inward corner, and the seven-ply strong region contains only
edge squares and inward corners. The existing corner-prison theorem
therefore leaves five symbolic families. On R's second rank, rook safety
requires x>=3 for K=(3,0). If K=(3,2), any rook farther right than K
has its attack on (1,2) blocked by K; that legal interior escape excludes
the apparent larger family. Distinctness excludes a rook on K itself.
Thus only R=(2,2) remains in that branch.

For a file-1 rook and K=(3,1), the weak escape (0,2), transposed to
(2,0), forces a strong king entry to a completely evaluated six-ply
second-edge region. Its coordinate inequalities require rook height
3 or 4. K=(3,2) admits all heights at least 3. The remaining diagonal
prison K=(3,3), R=(2,2) has the escape (0,0): neither a king move nor a
rook move can enter a six-ply corner region, and immediate mate is
impossible. Coordinate transposition supplies the other orientation.

For sufficiency, all legal weak replies lie among the five fixed edge
squares (0,0), (0,1), (0,2), (1,0), (2,0). At (0,0), move K to
(2,1) for a second-rank rook, and to (2,2) otherwise. The two near-corner
replies use the evaluated seven-ply near-corner region. At (2,0), move
R to (1,2). At (0,2), transpose coordinates and move K to (2,2) if
the original rook height is at most 4, and to (3,2) otherwise. Every
entry includes distinctness, king separation, rook safety and a legal
weak reply, so stalemate cannot masquerade as forcing.

The principal boundary checks are the adjacent protected rook (2,2),
the blocked rook ray for K=(3,2), and the original rook-height equality
4. No tablebase, engine, stored outcomes or diagnostic enumeration is
used as proof evidence. The Lean result checks the full coordinate
argument with symbolic rook inequalities. This result remains unfrozen.
