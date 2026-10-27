# Corner four-ply classification

Status: locally Lean-checked, unfrozen. This is a kernel statement;
history-aware outcomes and full KRK closure remain separate obligations.

For exact KRK, weak turn, W=(0,0) and king distance at least two, kernel
mate within four plies is equivalent to terminal checkmate or a root with
at least one legal reply satisfying one of these rows:

| Strong king S | Rook condition |
|---|---|
| (0,2) | R.y>=2 or R.x=2 |
| (2,0) | R.x>=2 or R.y=2 |
| (1,2) | R.y>=1 |
| (2,1) | R.x>=1 |
| (2,2) | R.x,R.y>=3; or R.x=0,R.y>=2; or R.y=0,R.x>=2; or R=(1,2) or (2,1) |
| (s,3), s<=2 | R=(2,1) |
| (3,s), s<=2 | R=(1,2) |

All coordinates are zero-based; squares are on the eight-by-eight board.
The rook and both kings are distinct. The table gives symbolic coordinate
conditions, not enumerated values for individual positions.

Necessity covers the sole inward neighbour (1,1) and applies the complete
near-corner three-ply formula to (1,0) and its transpose to (0,1), unless
those squares are covered. The resulting constraints imply the table or
terminal mate once nonempty replies are used. King file at least four
cannot satisfy both edge constraints and safe-rook necessity; the remaining
files split into their geometric king-rank cases.

The nonempty condition is essential in this argument. For R=(1,1), the
placements S=(0,2), (2,0) and (2,2) have no legal noncapturing weak model
reply. They would otherwise satisfy the universal condition on replies
vacuously. The formal necessity proof excludes these configurations using
an actual reply witness, rather than assuming that universal quantification
implies existence.

For sufficiency, the table implies a safe rook. Every legal weak reply is
(1,0) or (0,1); each reaches the appropriate complete near-corner three-ply
region. The exact kernel theorem retains existence of an actual legal
reply, with terminal mate handled by a separate disjunct.

The sources are `KRKFourPlyCorner.lean` (`corner_four_necessary`,
`corner_four_replies`) and `KRKFourPlyCornerKernel.lean`
(`corner_four_safe`, `weak_four_iff`). Geometric transposition transports
the kernel strategy only; it makes no assertion about transforming incoming
RAW repetition histories or castling flags.
