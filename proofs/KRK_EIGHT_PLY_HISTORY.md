# Weak-turn KRK at clocks at least 91

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. KRK remains open.

For every admitted ongoing RAW history s with exact KRK material, strong
colour sigma and weak colour sigma.opp to move, and endpoint halfmove clock
h>=91:

    ActualWin(sigma,s) iff KRKEightPlyHistory.Clear(s,K,R,W).

The complement is exactly the both-player holding region. The statement
retains all admitted incoming histories, both colours, all board orientations
and native kernel flags. It does not assert actual FIDE model correspondence.

## Closed coordinate/history test

The criterion is:

* the rook is safe;
* h<99 and the current repetition-key count is less than 3;
* for every geometrically legal weak king destination t, its exact native
  strong-turn key has incoming count less than 2, and the explicit
  `KRKEightPrefix.SevenAfterWeak` point/ray formula holds.

The point/ray formula is the [strong seven-ply criterion](KRK_SEVEN_PLY_HISTORY.md)
expressed in the ORIGINAL weak-root history. Its twenty king points and rook
inequalities are unchanged. All count terms now explicitly include the first
weak move's key indicator, then the strong move's key indicator and each
later prefix indicator. The separate current and intended claim conditions
are retained; the criterion is not just an ordinary distance bound.

`KRKEightPrefix.seven_append_iff` proves exact correspondence with the
strong seven-ply formula on the actual appended trace. Its intermediate
lemmas telescope every native occurrence count and clock threshold. Equality
of repetition keys is checked on actual `play` boards, never on normalized
coordinates or cleared castling flags. No history is reset or compressed.

## Necessity and sufficiency

Every weak winning root has a safe rook; otherwise a legal capture gives a
holding resource. The exact no-claim characterization gives the current
count, each intended child count, and h<99. Every actual defender reply must
remain winning. Its nonzeroing clock is h+1>=92, so the checked strong-turn
seven-ply outcome equivalence gives precisely `SevenAfterWeak` after the
prefix identity is applied.

Conversely the criterion excludes all current and intended weak claims.
Rook safety makes the geometric guarded king replies exhaustive over every
actual legal move. The seven-ply formula at each child supplies a clock-free
mate continuation, so that child is nondead and has a legal move; its clock
and occurrence bounds exclude automatic draws. The strong seven-ply RAW
certificate therefore applies. Retaining all defender replies gives the
eight-ply RAW certificate at the original weak root.

## Exact optimal distances

`high_clock_distance_cases` partitions the winning region into exact native
RAW distances 2,4,6,8: the last-reply region; otherwise the explicit four-ply
history criterion; otherwise the explicit six-ply history criterion; otherwise
the eight-ply criterion. Every case includes a certificate at that distance
and exclusion of the immediately preceding ply budget.

`KRKSixPlyExact.rule_six_iff` proves the six-ply coordinate/history formula at
all clocks, using the corresponding all-clock five-ply equivalence at every
child. Thus the lower-bound argument does not invoke a high-clock outcome
theorem outside its domain. Native weak seven-to-six parity preserves
ongoingness and claims, supplying the eight-ply lower bound.

Sources: `formal/EndgameChess/Rules/KRKEightPlyHistory.lean`,
`KRKEightPrefix.lean`, and `KRKSixPlyExact.lean`. All public main declarations
are registered in `formal/AxiomCheck.lean`. Local Lean 4.35.0 checks and the
integrated build pass (332 jobs), as does `lake env lean AxiomCheck.lean`.
New public main declarations report only `propext`, `Classical.choice`,
and `Quot.sound`. No freeze or hosted CI success is claimed.

Lower-clock outcomes, remaining terminal/capture correspondence, full FIDE
correspondence and global rule-aware WDL/DTZ remain open. KQK is unselected.
