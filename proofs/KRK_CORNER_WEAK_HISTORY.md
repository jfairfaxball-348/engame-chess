# Complete weak-corner late-clock history classification

Status: locally Lean-checked, unfrozen. Exact RAW win/draw classification
for either strong colour in this entire band; not full KRK closure.

Assume an ongoing admitted exact KRK history H, weak turn, W=(0,0), and
halfmove clock h>=95. Coordinates are zero-based. Let E=(1,0), N=(0,1),
and D=(1,1). Define the coordinate guard G(T) by:

    dInf(W,T)=1, T!=R, dInf(S,T)>=2,
    and the rook does not see T after the weak king moves there.

The clear-line condition uses only the three piece squares. With a safe
rook, these guards describe exactly all actual weak moves; every adjacent
square is E, N or D. Safety means dInf(R,W)>=2 or dInf(S,R)=1.

The strong side wins exactly when all the following conditions hold:

1. The rook is safe, h<99, and the root has fewer than three occurrences.
2. G(D) is false: the weak king has no legal inward escape.
3. If G(E), H contains fewer than two occurrences of the actual position
   after W->E, and the horizontal near-corner point/interval test below
   passes, with every query measured in H.
4. If G(N), H contains fewer than two occurrences after W->N, and the
   vertical near-corner point/interval test passes, again measured in H.

The two tests are completely evaluated finite coordinate formulas from
[the horizontal](KRK_NEAR_CORNER_FULL_THREE_PLY_HISTORY.md) and
[vertical](KRK_VERTICAL_NEAR_CORNER_THREE_PLY_HISTORY.md) slot tables.
An immediate-mate child uses its coordinate row without a later barrier.
Each nonmating king point or rook interval uses h<97 and two original
counts below two: the actual strong-entry key and the actual following
weak-return key. `KRKSlotPrefix` computes these from the original position
by first playing W->E or W->N, then the displayed slot moves. Its only
quantified destinations are the bounded ranks/files in those tables.
There is no future outcome or legal-move predicate in the winning test.

On the complement of this formula, both players have RAW holding policies.
For any win, distance is exactly two plies in LastReply and exactly four
otherwise. The checked corner LastReply formula itself has two coordinate
rows, so the distance test also introduces no future outcome predicate.

## Necessity against all alternatives

A RAW win projects to a kernel win, which forces rook safety. Every actual
weak reply is therefore a noncapturing canonical king move. All current
and intended root claims must be absent. Because an actual reply exists,
the intended fifty-move test gives h<99. The current repetition count is
below three and each available reply's original key count is below two.

If D is available, the resulting strong history has clock at least 96.
A win there would have a three-ply certificate. Its geometric region has
the weak king on an edge, contradicting D's depth one. For E and N, the
complete strong-history slot criteria are necessary. The original-prefix
identity evaluates both later keys back in H: the first appended key has
the opposite turn to the strong-entry key and a different weak king square
from the following return key. All flag updates are those of actual play.

## Sufficiency, admission and distance

The displayed counts and time bounds exclude every actual root claim.
The ongoing hypothesis supplies a legal root reply; it does not follow
from a vacuous universal condition. Safety and the missing inward escape
leave only E/N. Their evaluated slot tests supply three-ply certificates
on their actual appended histories. The proof establishes child ongoing
status from its kernel mate certificate, a legal-move witness, clock bound
and updated repetition count. It then constructs one uniform four-ply
RAW certificate for all root replies.

LastReply plus absence of root claims gives a two-ply certificate; a
nonterminal weak-turn root cannot win within one. Outside LastReply,
the exact weak-three equivalence rules out winning within three. The
win/hold duality and universal strong holding policy give the draw result.

## Formal correspondence

`KRKCornerWeakBand.lean` defines `Guard` and `CornerClear`; its main
declarations are `high_clock_force_iff`, `high_clock_actual_iff`,
`high_clock_hold_iff`, `high_clock_draw_iff`, and
`high_clock_distance_cases`.

`KRKSlotPrefix.lean` evaluates the two appended near-corner slot tests in
the original trace. `KRKWeakBranch.lean` proves their admission and uniform
three-ply certificates. The earlier full corner four-ply board theorem
remains valid; this proof directly combines all finite neighbour guards
with the complete child formulas instead of splitting king/rook families.

The remaining weak W=(1,0) band, other actual orientations, lower clocks,
full FIDE-rule correspondence and global WDL/DTZ semantics remain open.
