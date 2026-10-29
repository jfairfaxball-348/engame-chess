# Seven-ply geometry and the next eight-ply destination problem

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. These are supporting geometric results for the
next positive-clock band; KRK remains open.

For every exact KRK kernel board q with strong colour sigma to move,
separated kings d(K,W)>=2 and no rook check on the weak king,
`KRKSevenGeometry.kernel_seven_iff` proves that mate is forceable within
seven plies exactly when `KRKSevenGeometry.Clear(K,R,W)` holds.

This formula is immediate mate, or an ordinary king entry into one of twenty
fixed canonical points in the [complete weak six-ply region](KRK_GLOBAL_SIX_GEOMETRY.md),
or a rook-line intersection with that region. Each destination must be safe
and have a legal weak reply. Every geometric first move is proved legal;
every winning nonmating first move is covered. The actual castling exclusion
uses `KRKCastleSix.castle_not_six`. Native kernel flags are retained; only
coordinate predicates use the existing frames. No incoming history is part
of this clock-free assertion.

The point rectangle {0,...,4} x {0,...,3} follows from the symbolic six-ply
tables. It is a finite king-point catalogue with rook inequalities, not an
atlas of position outcomes. The proof is the same geometric entry analysis
used by the native [seven-ply history theorem](KRK_SEVEN_PLY_HISTORY.md), with
the history conditions removed and both directions checked independently.

`KRKEightGeometry.kernel_eight_iff` gives the exact INTERMEDIATE guard form
for a nonmated weak root: safe rook, a nonempty legal reply set, and the
complete seven-ply coordinate test after every geometrically legal reply.
This form still needs reduction to a compact eight-ply destination catalogue.
It does not by itself certify the next strong/weak clock band.

The same module proves clock-free parity: strong eight-ply forcing is
equivalent to seven-ply forcing, and weak nine-ply forcing implies eight-ply
forcing. The converses follow by budget monotonicity. These retain every
defender reply, rather than relying on a selected policy.

Sources: `formal/EndgameChess/Rules/KRKSevenGeometry.lean` and
`formal/EndgameChess/Rules/KRKEightGeometry.lean`. Main declarations are in
`formal/AxiomCheck.lean`. The Lean 4.35.0 integrated build passes (332 jobs),
and `lake env lean AxiomCheck.lean` passes. New public main declarations report
only `propext`, `Classical.choice`, and `Quot.sound`.

Next: evaluate the eight-ply destination geometry and investigate actual
castling entries at that larger budget before constructing the strong h=90/91
and weak h=89/90 native criteria. Do not assume the six-ply castling exclusion
extends to eight. Lower clocks, full FIDE correspondence and global WDL/DTZ
remain open. No freeze or hosted CI success is claimed.
