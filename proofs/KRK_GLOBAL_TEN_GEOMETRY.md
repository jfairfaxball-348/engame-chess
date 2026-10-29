# Full-board ten-ply KRK geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

The current Lean proof establishes `KRKTenGlobal.kernel_ten_iff`: for any native KRK position with the weak player to move and kings separated by at least two king steps, mate can be forced within ten plies iff the board is already terminal or lies in `KRKTenGlobal.Region`. Native flags remain in the quantified position.

For an interior weak king, use the proved canonical first-strip frame. Only inward-corner and near-strip destinations survive; their rook inequalities are evaluated by `KRKTenInner` and `KRKTenNearStrip`. Deeper squares and central first-strip squares are excluded by all-move lower bounds.

For an edge weak king, normalize to rank zero and file at most three. The five compass replies must pass the fixed `KRKTenEdge.NineTest` catalogue. Its inward alternatives use the evaluated six-point inward-nine and near-strip-nine inequalities. Edge alternatives use `KRKNineEdge`: forty fixed king points and rook-line intersections with the proved eight-ply edge region. This remains a finite symbolic point/ray catalogue, not a simplified inequality list at every edge. It contains no future winning predicate, move evaluator or enumerated outcome values.

`kernel_exact_ten_iff` subtracts the entire eight-ply region (including terminal boards). Weak-turn parity proves that nine adds nothing to eight, so this gives the matching exact-ten lower bound. `region_live` explicitly prevents stalemate from entering the winning region.

`KRKCastleTen` audits both native castling directions for both colours. First, two pieces sharing an outer board line cannot form a winning ten-ply interior family. More strongly, either actual castled king/rook configuration cannot win within nine plies against an interior weak king. A weak interior escape therefore forces edge confinement. Kingside castling has no ten-ply winning destination; queenside castling would require the weak king on the rook's original corner, contradicting the source board. Thus no legal actual castle enters a nonmating weak-ten win. No castling-right erasure is used for this audit.

These are bounded geometric results. They do not settle full KRK, all incoming-history barriers, FIDE correspondence or exact global distances. No result here is frozen or source-pinned.
