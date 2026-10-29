# Complete clock-free weak six-ply geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. KRK remains open.

For every exact KRK kernel position q, strong colour sigma, weak turn and
king separation d(K,W)>=2, `KRKSixGlobal.kernel_six_iff` proves:

    MateWithin(sigma,6,q)
      iff Terminal(K,R,W)
          or [Region(K,R,W) and SafeRook(K,R,W) and Live(K,R,W)].

Here `Live` means there is a legal noncapturing weak king reply. Combined
with rook safety it exactly prevents stalemate/capture omissions. `Terminal`
is the previously proved explicit coordinate mate formula, handled first.

`Region` has no outcome, minimax or legal-move search predicate. On an edge,
normalize only the three coordinates to rank zero, files 0 through 3, and use:

* file 0: the twelve-point [corner table](KRK_CORNER_SIX_GEOMETRY.md);
* file 1: the [near-corner table](KRK_NEAR_SIX_GEOMETRY.md);
* file 2: the [second-edge table](KRK_SECOND_SIX_GEOMETRY.md);
* file 3: the already evaluated central-edge four-ply region.

In the interior, only the four inward-corner weak squares can qualify. Map
their coordinates to W=(1,1) and use exactly K=(3,1), y_R=2, x_R>=3, or
K=(1,3), x_R=2, y_R>=3, as proved in the
[interior criterion](KRK_INWARD_CORNER_SIX_GEOMETRY.md).

## Exact distance six

Let `EarlierFour` be edge depth zero together with the explicit normalized
four-ply `KRKFourGeometry.Shape` formula. The global exact-distance theorem is:

    MateWithin(sigma,6,q) and not MateWithin(sigma,5,q)
      iff Region and SafeRook and Live and not EarlierFour.

All terms on the right are geometric coordinate/reply tests. The subtraction
is of the already proved finite coordinate formula, not an unevaluated value
recurrence. The five-to-four weak-turn parity theorem supplies the matching
lower bound. A live root cannot already be mated.

## Coordinate transport and rule scope

`KRKFrameBound.bound_transport` extends the checked same-budget geometric
transport argument to the existing `Frame` type, whose inverse is separate
from its forward map. This is necessary for rotations composed of a reflection
and transposition. It uses only the frame's inverse, distance, visibility and
step properties, and induction on the stated mate budget. The source board
in this transport lemma is explicitly castling-free; the target may retain
arbitrary flags.

The applications construct castling-free synthetic boards from coordinates.
`five_map` and `six_map` then transport only pure geometric predicates. The
actual position q, rights, clocks, history and repetition keys are never
transformed. The final six-ply kernel theorem retains the actual q and its
native flags. Existing proofs of the five-ply kernel criterion supply all
strong alternatives, including their castling analysis.

Each canonical region has both necessity and sufficiency. The frame is a
bijection, so every original weak reply has a mapped reply and conversely.
The proof preserves the nonempty defender branch and uses exact visibility,
including king blockers, throughout the sufficient directions.

Sources: `formal/EndgameChess/Rules/KRKFrameBound.lean` and
`formal/EndgameChess/Rules/KRKSixGlobal.lean`. The main equivalence and global
exact-distance theorem pass the local Lean 4.35.0 checker. The integrated
`lake build` passed (322 jobs), and `lake env lean AxiomCheck.lean` passed.
New public main declarations report only `propext`, `Classical.choice`, and
`Quot.sound`.

This completes the clock-free weak six-ply geometry, not the next full-history
clock band or KRK. Native incoming-history barriers, lower clocks, FIDE model
correspondence and global rule-aware WDL/DTZ remain open. No freeze or hosted
CI success is claimed.
