# KRK bounded frontier: proof correspondence and certification scope

2026-10-29. Supporting-results bundle EC-T0049. KRK remains OPEN.

The exact complete-module and public-theorem inventory is
[KRK_BOUNDED_FRONTIER_SCOPE.json](KRK_BOUNDED_FRONTIER_SCOPE.json). It contains
213 modules and 1,147 public theorem statements added since the EC-T0048 proof
source. These counts describe the certification boundary, not solved positions
or a percentage of KRK. All definitions, private lemmas and complete source
bytes in those modules are preserved by the pinned source and hash inventory.
Earlier frozen sources and manifests remain unchanged.

## Statements, domains and correspondence

Coordinates are zero-based `Fin 8` pairs. `sk`, `rs`, `wk` denote the strong
king, rook and weak king. `MateWithin sigma n q` is the existing alternating
legal-move mate predicate in at most `n` board plies; a weak nonterminal node
requires a legal reply and all legal replies satisfy the continuation.
An exact distance assertion additionally excludes the preceding budget using
the proved parity reductions. King separation, distinct material squares,
turn and nonchecking legality assumptions in each declaration are retained.
Frame transport is board geometry, not an unproved symmetry of raw histories.

| Result | Principal Lean entry points | Mathematical argument / paper |
|---|---|---|
| Exact terminal and immediate-mate geometry; native move/history interfaces | `KRKMateGeometry.kernel_mate_iff`, `KRKImmediate`, `KRKImmediateHistory`, `KRKDeadline` | Exact board mate and legal rook-ray tests; deadline preserves the same incoming history. [Deadline](KRK_EXACT_CLOCK_DEADLINE_S092.md). |
| Complete six/eight/ten/twelve-ply board criteria | `KRKSixGlobal`, `KRKEightGlobal`, `KRKTenGlobal`, `KRKTwelveGlobal` | Classify every weak-square frame, require rook safety and a live weak reply, and verify every guard. Papers [six](KRK_GLOBAL_SIX_GEOMETRY.md), [eight](KRK_GLOBAL_EIGHT_GEOMETRY.md), [ten](KRK_GLOBAL_TEN_GEOMETRY.md), [twelve](KRK_GLOBAL_TWELVE_GEOMETRY.md). |
| Odd-ply entries and exact bounded distances | `KRKSevenGeometry`, `KRKNineGeometry`, `KRKElevenGeometry`, `KRKThirteenGeometry`; corresponding `PlyExact` modules | Immediate mate or an actual ordinary king/rook entry into the preceding even-ply region. Point/ray catalogues are fixed coordinates and symbolic regions, not stored outcome values. Exact lower bounds subtract the preceding region using parity. |
| Actual RAW history criteria through strong thirteen / weak fourteen | `KRKThirteenPlyHistory.high_clock_actual_iff`, `.high_clock_draw_iff`; `KRKFourteenPlyHistory.high_clock_actual_iff`, `.high_clock_draw_iff`; corresponding `PlyExact` modules | Turn-dependent deadline, original-trace current/intended claims, actual legal continuations, all weak replies and matching holding complement. [Thirteen/fourteen history](KRK_THIRTEEN_FOURTEEN_PLY_HISTORY.md); earlier seven/eight, nine/ten and eleven/twelve papers are dependencies. |
| Full deep fourteen-ply geometry and exact additions | `KRKFourteenDeepExact.kernel_fourteen_iff`, `.kernel_exact_fourteen_iff` | Covered-neighbour exclusions eliminate the depth-two belt except second corners; explicit opposition entries and lower bounds finish those corners. [Deep proof](KRK_FOURTEEN_DEEP_EXACT.md). |
| Full canonical central first strip at fourteen plies | `KRKFourteenCentralExact.kernel_fourteen_iff`, `.kernel_exact_fourteen`, `.framed_clear_iff` | Necessary prison, all strong-entry lower bounds and explicit entries for each surviving family. [Central proof](KRK_FOURTEEN_CENTRAL_STRIP.md). |
| Full canonical near strip at thirteen plies | `KRKThirteenNearStrip.kernel_thirteen_iff`, `.kernel_exact_thirteen` | Five king points; complete constructive rook-ray inequalities; exact subtraction of the eleven-ply region. Argument below. |
| Partial inward thirteen-ply ray analysis | `KRKThirteenInnerRook.high_destination`, `.rook_line_necessary` | Ten horizontal king profiles; necessary ray inequalities and a constructive universal ray only at the high profile. Argument and limits below. |

For the history results, quantify over **every admitted ongoing RAW history**
with exact KRK material, either strong colour and all orientations/native flags.
The strong-turn criterion is complete when `h >= 86`; the weak-turn criterion
is complete when `h >= 85`. Winning distances there belong respectively to
`{1,3,5,7,9,11,13}` and `{2,4,6,8,10,12,14}`. The unrestricted bounded-certificate
iff theorems retain their budgets without asserting that these bands cover all
clocks. The history certificates remain part of the criteria: a board region
alone is not a win with an arbitrary incoming repetition history.

Actual native castling is excluded as a nonmating short-budget entry by
`KRKCastleFour`, `KRKCastleSix`, `KRKCastleEight`, `KRKCastleTen` and
`KRKCastleTwelve`. Their hypotheses concern the actual legal native move and
flags; a no-rights canonical board is not substituted for that necessity step.

## Newly completed near thirteen-ply profile

Normalize the weak king to `(1,2)`. The twelve-ply target region has five
strong-king profiles: `(3,1)`, `(3,2)`, `(0,4)`, `(1,4)`, `(2,4)`.
`KRKThirteenNearRook.RookRegion` gives their exact rook regions and
`KRKThirteenNearStrip.region_shape` proves equivalence with the complete
twelve-ply near region. A thirteen-ply king entry is a unit Chebyshev king
step to one of those points, distinct from the rook, satisfying its region.

For rook entries, expand `RookSees` into alignment, non-nullness and strict
segment obstruction by the two kings. `rook_line_necessary` derives the
source inequalities from every possible destination. `rook_destination`
constructs a destination for every listed source condition. These targets
are proved distinct from both kings. At the side profile, file-one targets
have rank zero or rank at least four. The source `(1,0)` itself cannot move to
the rank-zero target, and a ray to rank four crosses the weak king; it is
therefore excluded from that file entry. Horizontal access to `(3,2)` must
start to the right of the weak king; vertical access to `(2,3)` must not cross
the strong king `(2,4)`. The inequalities record both obstructions explicitly.

Immediate mate is impossible at this interior weak square. Thus the complete
native thirteen-ply iff follows from the general entry theorem. The
exact-thirteen theorem excludes the complete eleven-ply region, using the
strong twelve-to-eleven parity reduction; it does not merely exhibit a
thirteen-ply strategy.

## Inward ray result: exact partial boundary

At weak king `(1,1)`, the ten horizontal target king profiles are
`(3,0)`, `(3,1)`, `(3,2)`, `(3,3)`, `(4,1)`, `(4,2)`, `(0,4)`, `(1,4)`,
`(2,4)`, `(1,5)`. `RookRegion` names their existing twelve-ply target regions.
For every source distinct from the profile king, `rook_line_necessary` proves
that a clear ray into that profile region satisfies `RookCondition`.
It is **only a necessary implication**, not the complete inward thirteen-ply iff.

At the high profile `(3,2)`, `high_destination` constructs a target from every
rook source. On source rank zero choose file four or five different from the
source; on rank one use file four/five when the source is right of file one,
otherwise move vertically to rank three. From rank two move to rank three.
From ranks at least three choose file two or three different from the source.
Each construction proves a non-null clear ray, target distinct from both
kings, and membership in `KRKTwelveInnerHighExact.Region`. The target region
itself can contain a colliding square when considered without material
hypotheses; the explicit distinctness checks are essential. Constructive
sufficiency for the other nine profiles and the transposed aggregate theorem
remain open and are not implied by this freeze.

## Critique, trust and verification

The correspondence review is by the same agent; no independent external audit,
hosted CI or Palomar success is claimed. This bundle uses core Lean 4.35.0,
no external packages, and accepts only `propext`, `Classical.choice`, `Quot.sound`.
Certification captures a clean pinned-source full build, all public theorem
types and axiom reports, source hashes, commands and exit codes in the manifest.
No tablebase, chess-engine oracle, stored position-value atlas, `sorry`,
`admit`, ad hoc proof axiom or unsafe escape is admitted.

The fixed-barrier/least-rank arbitrary-history reduction remains paper only.
Lower-clock global outcomes, full FIDE correspondence, global exact distance
and KRK class closure remain open. See the [KRK status](../docs/KRK_COMPLETION.md).
