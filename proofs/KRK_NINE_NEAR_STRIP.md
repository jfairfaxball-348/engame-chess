# Exact nine-ply forcing next to an inward corner

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For W=(1,2), a strong-turn KRK board with distinct pieces and king
separation at least two forces mate within nine plies exactly when:

* R=(x,3), x>=3, and K is one king step from (3,1); or
* K=(3,1) and the rook has rank 3, file at least 4, or file 3 and
  rank at least 2.

`KRKNineNearStrip.kernel_nine_iff` proves both directions. The complete
weak-turn eight-ply criterion at this square forces the first move to
enter K=(3,1), R=(x,3), x>=3. `KRKNineEntry.eight_entry_move` treats
all legal native moves and excludes actual castling through the existing
eight-ply castling obstruction. An interior weak square cannot be an
immediate mate. Ordinary king entries give the first alternative.
Ordinary rook entries give the second after eliminating their destination
by a rook-line calculation; a file-3 rook below the strong king is
blocked, so rank 0 is correctly excluded.

Conversely, the king move to (3,1) is legal in the first alternative.
For the second, a rank-3 rook moves to file 3 or 4 on its rank; any
other rook moves on its file to rank 3. The inequalities ensure an
unblocked ray. The eight-ply near-strip theorem then supplies forcing.

For a nonchecking strong root, `kernel_exact_nine` also proves the
matching lower bound: strong eight-ply forcing equals seven-ply forcing,
whose weak-square domain contains only edges and inward corners. W=(1,2)
belongs to neither. Thus every winning board in this criterion has exact
clock-free distance nine. The criterion retains native flags but has not
yet evaluated incoming-history barriers. It remains unfrozen.
