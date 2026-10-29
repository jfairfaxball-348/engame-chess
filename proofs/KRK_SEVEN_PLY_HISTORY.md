# Strong-turn KRK at clocks at least 92

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. KRK remains open.

For every admitted ongoing RAW history s with exact KRK material, strong
colour sigma to move, and endpoint halfmove clock h>=92:

    ActualWin(sigma,s) iff KRKSevenPlyHistory.Clear(s,K,R,W).

The complement is exactly the region where both colours have RAW holding
strategies. No FIDE correspondence or full KRK closure is claimed.

## Evaluated criterion

`Clear` is an immediate mating rook move, or a king entry, or a rook entry
into the [complete geometric weak six-ply region](KRK_GLOBAL_SIX_GEOMETRY.md)
with the original-history test below.

Choose the existing coordinate frame for W: edge normalization to rank zero,
files 0 through 3, or the inward-corner reflection for interior squares.
All winning six-ply destinations have strong-king coordinates in the twenty
fixed points {0,...,4} x {0,...,3}. This bound follows from the explicit region
tables; it contains no enumerated position values. Nonwinning points are
excluded by the same closed rook inequalities and weak-square conditions.

The king-entry formula tests distance one to one of these points, distinctness
from the rook, king separation, the geometric region, a legal weak reply and
the native history test. The rook-entry formula fixes the strong king at one
of these points and tests rook-line coordinates/intersections with that region.
The coordinate frame never transforms actual rights, clocks or history keys.

Thus there is no legal-move search or future win/draw predicate in `Clear`.
Its quantified coordinates are twenty fixed king points, rook lines, and
geometrically guarded defender replies in already evaluated finite regions.

## Original history and claims

Let H be the entire incoming trace and m the proposed first strong move.
Let B1=play(q,m), and C1(k)=count_H(k)+[key(B1)=k]. The immediate six-ply child
history test requires:

* a safe rook, h<98 and count_H(key(B1))<2;
* for every legal weak king reply t, C1(key(B2))<2, where B2 is the actual
  native board after that reply;
* the explicit strong five-ply point/ray formula at B2, with every subsequent
  prefix indicator retained in the original H counts.

`KRKSevenPrefix` expands those later counts: its `firstOccurrences` is C1
plus the B2 indicator, and `secondOccurrences` additionally includes the next
strong child B3. Later entry tests use these exact counts. No old occurrence
is discarded. No assumption of distinct future keys replaces a count.

The lemmas culminating in `six_append_iff` prove this formula equivalent to
the previously checked native `KRKSixPlyHistory.Clear` on the actual appended
trace. All strong KRK moves here are nonzeroing, so appending m increments
the clock; the translated strict thresholds are proved, not guessed.

The root strong player may decline an optional current claim. The formula
does not forbid that root. Weak current and intended claims are retained by
the exact six-ply child criterion, and immediate mate retains precedence.

## Both directions and distance

For sufficiency, each point/ray entry determines a legal ordinary move.
The geometric six-ply result supplies a real mate continuation and a legal
weak reply, so the child is nondead and nonstalemated. The explicit count and
clock inequalities exclude automatic endpoint draws. The six-ply RAW
certificate lifts to the original strong root, giving a seven-ply certificate.

For necessity, every winning strong move preserves KRK and increments the
clock. A nonterminal child therefore has h_child>=93. The deadline and
weak-turn parity put it in the six-ply geometry; the checked native weak
criterion supplies exactly the expanded history test. Castling cannot be a
nonmating winning entry here, by `KRKCastleSix.castle_not_six`. All remaining
king and rook moves are covered by the twenty-point/rook-line description.
Terminal winning children give the immediate-mate branch.

`high_clock_distance_cases` gives exact optimal winning distances 1,3,5,7:
immediate mate; otherwise the explicit three-ply history region; otherwise
the explicit five-ply history region; otherwise the seven-ply region.
Each case includes its RAW certificate and exclusion of the preceding ply
budget. `KRKFivePlyExact.rule_five_iff` proves the five-ply coordinate/history
formula at every clock, so the seven-ply lower-bound argument does not misuse
the older high-clock-only outcome theorem. Native strong six-to-five parity
preserves all claim and ongoingness conditions.

Main source: `formal/EndgameChess/Rules/KRKSevenPlyHistory.lean`, with
`KRKSevenPrefix.lean`, `KRKSevenSlots.lean`, `KRKSevenEntry.lean`, and
`KRKFivePlyExact.lean`. All public main declarations are registered in
`formal/AxiomCheck.lean`. Local Lean 4.35.0 checks and the integrated build
pass (332 jobs), as does `lake env lean AxiomCheck.lean`. New public main
declarations report only `propext`, `Classical.choice`, and `Quot.sound`.
No freeze or hosted CI result is claimed.

Weak clocks 91/92 are covered by the [eight-ply result](KRK_EIGHT_PLY_HISTORY.md).
Lower clocks, terminal/capture coverage beyond the current ongoing scope,
FIDE correspondence and global rule-aware WDL/DTZ remain open.
