# Full-board nine/ten-ply original-history outcomes

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For every admitted ongoing RAW KRK history, both colours and all board
orientations, the new criteria are:

* Strong turn, halfmove clock h>=90: actual strong-side win iff
  `KRKNinePlyHistory.Clear`; otherwise both players can hold.
* Weak turn, halfmove clock h>=89: actual strong-side win iff
  `KRKTenPlyHistory.Clear`; otherwise both players can hold.

These extend the former h>=92/91 bands. They do not settle lower clocks,
full FIDE correspondence, terminal/capture coverage or global WDL/DTZ.
All results in this proof remain unfrozen.

## Geometry and history formula

The [complete eight-ply board region](KRK_GLOBAL_EIGHT_GEOMETRY.md) is a
coordinate formula: interior families or five fixed edge compass tests,
whose seven-ply destinations are fully evaluated point/rook inequalities.
`KRKNineSlots.region_rank` proves that a king in this eight-ply region
has canonical rank at most four. On edges its frame is the existing
edge normalizer; on interior squares it is the proved first-strip frame.
This supplies forty fixed candidate king points, with actual rook
coordinates left symbolic. The bound follows from the explicit seven-ply
destination catalogues, not a board enumeration.

`KRKNineGeometry.Clear` consists of immediate mate, one of those king
entries into the eight-ply region, or a rook-line intersection with that
region. All alternatives preserve distinct pieces, both blockers, king
separation and the native move model. Necessity excludes actual castling
by the eight-ply castling theorem and treats every legal ordinary king
and rook choice. Sufficiency constructs the indicated legal move.

`KRKNinePlyHistory.Clear` adds `After` at each nonmating entry. `After`
is the already evaluated eight-ply clock/key-prefix formula on the
original trace with this specified move appended. Its proof quantifier
ranges only over proofs of legality of that one move. It neither searches
over moves nor refers to a future winning predicate. Expanding the
definitions gives only fixed geometric tests, native key equalities,
clock inequalities and original occurrence counts.

`KRKTenPlyHistory.Clear` requires a safe rook, the exact weak current
claim exclusions, every intended-claim exclusion at a legal weak king
destination, and the nine-ply prefix formula after that move. The weak
destinations are the adjacent geometric guard squares. The original
trace is retained throughout, including native flags and keys; the
coordinate frames never rewrite a history.

## Necessity and sufficiency

At strong h>=90, every winning nonmating child is quiet and has clock
at least 91. The exact deadline gives at most nine plies in that weak
child, and weak parity reduces nine to eight. The complete eight-ply
geometry and original-history criterion give the stated root entry.
Immediate mate is kept separately, including mate precedence over draw
thresholds. Optional strong-side claims can be declined.

At weak h>=89, a winning history must exclude all current and intended
claims. Every legal safe-rook weak move is quiet, with child clock at
least 90. The strong nine-ply outcome theorem therefore evaluates every
defender branch. Rook captures are excluded only by the already proved
necessary rook-safety condition for actual forcing; they remain drawing
resources outside the winning region.

Conversely, the geometric entry gives a live eight-ply child. Its
explicit clock/key tests guarantee that the appended history is ongoing,
and the checked eight-ply certificate supplies its continuation. The
weak ten-ply certificate checks every legal reply and every claim before
using the nine-ply child certificates. Finite KRK termination duality
then proves both-player holding on each complement.

## Exact distance

`KRKSevenPlyExact.rule_seven_iff`, `KRKEightPlyExact.rule_eight_iff`,
`KRKNinePlyExact.rule_nine_iff` and `KRKTenPlyExact.rule_ten_iff`
hold for bounded forcing certificates at every clock, without the
high-clock assumptions needed for the unbounded actual-win equivalence.
Their necessity proofs use the supplied certificate's child budget,
not a high-clock deadline. This distinction is needed for valid lower
bounds in the new bands.

Strong rule-aware eight equals seven; weak nine equals eight; strong ten
equals nine; weak eleven equals ten. Each follows directly from turn
alternation and the previous parity theorem, preserving claims and
ongoing-state obligations.

The exact winning distances in the strong band are 1,3,5,7,9, and in the
weak band 2,4,6,8,10. The new terminal cases are respectively the nine-ply
criterion minus the seven-ply criterion and the ten-ply criterion minus
the eight-ply criterion. `high_clock_distance_split` exposes these
tests; `high_clock_exact_distance` proves the finite distance alternatives
with a matching exclusion of the preceding ply. Earlier distance cases
are supplied by the unrestricted seven/eight-ply certificate theorems.

## Boundary critique

Nonempty defender replies are proved for every eight-ply destination;
the coordinate region is never used as permission to force through
stalemate. Dependently typed append legality is transported only for
the same concrete move. No history is normalized, no old occurrence is
discarded, and no clock-zero policy is assumed to avoid incoming keys.
All proof obligations are checked in Lean with the pinned toolchain;
diagnostic computation, engine or tablebase values supply no proof data.
This is an explicitly bounded clock-band result, not the full KRK claim.
