# Eight-ply deep-interior exclusion and a new strip family

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. KRK remains open. These results advance the open
eight-ply destination catalogue; they are not its complete classification.

## Complete deep-interior exclusion

For every exact KRK kernel position with weak turn and separated kings,
`KRKEightInterior.weak_eight_depth_le_one` proves:

    MateWithin(sigma,8,q) implies edgeDepth(W)<=1.

At a nonmated weak eight-ply root, every legal reply must admit strong
seven-ply forcing. Such a reply is either on an edge or at one of the four
inward corners. Therefore every other interior neighbour must be covered by
the strong king or a rook line (`covered_or_inner`).

If W has edge depth at least two, its four orthogonal neighbours are all
interior and none is an inward corner. All four must be covered. With
separated kings, their coordinate constraints force the rook onto W itself,
contradicting exact material. This uses four symbolic neighbours, not an
enumerated outcome atlas. Terminal mate is excluded independently by its
proved edge-depth-zero property.

`KRKEightInteriorHolding.high_clock_deep_holding` then proves actual RAW
drawing for every admitted strong-turn history with h>=90 and edgeDepth(W)>=2:
both colours can hold, and the strong colour has no actual win. The deadline
gives at most ten plies; a strong first move leaves weak W unchanged and a
weak nine-ply child, which parity shortens to eight. No incoming repetition
history, optional/current/intended claim, or native flag is discarded.

## A genuinely new first-strip region

Let W=(1,2), K=(3,1), R=(x,3) with 3<=x<=7. For every exact-material kernel
board of either colour, weak turn:

    MateWithin(sigma,8,q) and not MateWithin(sigma,7,q).

This is `KRKEightStrip.kernel_exact_eight`. The rook is safe and the only
legal weak replies are (0,1), (0,2), and (1,1): the rook's third rank and the
strong king exclude all remaining neighbours.

After either edge reply, move K to (2,2). For W=(0,1), transposition gives
the checked near-corner six-ply diagonal-king region. For W=(0,2), it gives
the second-edge diagonal-king region with rook height x>=3. Every destination
has a specific legal weak reply and a safe rook.

After W=(1,1), move R from (x,3) to (x,2). The king does not block that rook
move, including x=3. This is exactly the checked inward-corner six-ply region
K=(3,1), rook rank two and file at least three. Thus every weak reply can be
answered by a strong move into a six-ply region, giving eight plies.

The lower bound uses the previously proved weak seven-to-six parity and
the complete interior six-ply restriction: W=(1,2) is not an inward corner.
Consequently no strategy can force mate within seven, independently of the
chosen sufficient entries above.

This family shows why the earlier six-ply interior classification cannot be
reused unchanged at eight plies. The first strip really acquires new winning
boards. It does not assert that these are all eight-ply strip boards, and no
native-history win is inferred from this clock-free family alone.

Sources: `KRKEightInterior.lean`, `KRKEightInteriorHolding.lean`, and
`KRKEightStrip.lean` in `formal/EndgameChess/Rules/`. All main declarations
are in `formal/AxiomCheck.lean`. The Lean 4.35.0 integrated build passes
(338 jobs), and `lake env lean AxiomCheck.lean` passes. New public main
declarations report only `propext`, `Classical.choice`, and `Quot.sound`.
No freeze or hosted CI success is claimed.

Remaining: exact first-strip/corner/edge eight-ply regions, native strong
h=90/91 and weak h=89/90 outcomes, lower clocks, FIDE correspondence and
global rule-aware WDL/DTZ.
