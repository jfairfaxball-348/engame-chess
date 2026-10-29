# Direct KRK frontier after the integrated clock0 result

**ARCHIVED, beyond parity (owner, 2026-10-29).** Arbitrary clocks, incoming histories and claims are outside the [outcome target](../docs/CHARTER.md#parity-target-hard-boundary-owner-2026-10-29). Kept as a research record; not an open obligation. Current work: [KRK status](../docs/KRK_COMPLETION.md).

Historical route: 2026-10-21. Research admission / OPEN problem, not a new theorem candidate.

Current update (2026-10-29): EC-T0049 freezes bounded history-aware strong h>=86 / weak h>=85 criteria and the supporting geometric frontier. The deadline is included in that bundle. The fixed-barrier least-rank reduction below remains paper only. See [KRK status](../docs/KRK_COMPLETION.md); the historical wording below describes the original route, not the current certification status.
The full continuing objective is unchanged. No new foundation is admitted here.

## Exact next missing claim

For EVERY admitted KRK history, both turns/colours and every endpoint clock,
give a compact explicitly evaluated criterion for actual win/draw, with a
correct winning or holding strategy and the relevant distance conventions.
The criterion must depend on the real board, clock and incoming history when
necessary. A rename of W, a bounded minimax recurrence, per-position atlas,
exhaustive search or generic W/policy equivalence is not that characterisation.
Preserve all legal rook captures, terminal/claim branches and intended claims.

The wall93/arrivals97-98 result settles the geometric cap needed for clock0,
not the positive-clock classification. Another slightly faster sufficient
policy would still leave necessity and arbitrary history unresolved. Do not
select that as a default easier milestone. The remaining work must evaluate
the actual unknown domain rather than add another conditional certificate.

## Direct obstacles the proposed criterion must resolve

1. A nonoptimal mate ceiling does not determine whether a faster strategy
   beats a given remaining claim threshold. Need matching lower bounds against
   ALL strong move alternatives on any region declared drawn for lack of time.
2. Incoming repeated keys may permit a weak CURRENT claim or an INTENDED
   claim after announcing a legal move, including a move to a strong-turn key.
   A key-simple future policy alone says nothing about those old occurrences.
3. A strong side may decline its own optional claim. A blanket ban on all
   claimable roots is not a necessary criterion. Automatic endpoint draws and
   mate precedence must remain distinct from optional claims.
4. A claim using the exact FIDE repetition key cannot be replaced by a claim
   about arbitrary raw flags. The full board/correct-claim correspondence is
   an explicitly necessary part of the eventual all-history result, still OPEN.
5. Any region formula based on a chosen geometric policy needs a dominance
   argument against other legal strong choices before it supplies necessity.
   Failure of the chosen policy is not a draw proof.

The selected route now has a [complete paper reduction](../proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md)
and [separate same-agent audit](../audits/KRK_STATIC_HISTORY_REDUCTION_S092_PAPER.md):
use the exact turn-dependent deadline and fixed barriers at keys already seen
at least twice in the ORIGINAL history, exempting the initial root and mate
leaves. Weak-root current claims are checked separately. Sufficiency requires
a least-rank policy for the fixed-barrier objective, making future keys simple;
it does NOT assume the old unconstrained clock-free policy avoids old keys.
The normalized-key exact legal-child interface is already frozen, so a generic
history-loop-removal framework is unnecessary. This reduction is PAPER ONLY
and remains unformalised; its fixed-barrier mate condition is NOT an explicitly
evaluated geometric formula and does not close the outcome obligation.

[EC-C053 deadline](../proofs/KRK_EXACT_CLOCK_DEADLINE_S092.md) is the one admitted
necessary time dependency, with local Lean checks only: winning requires
budget max(1,100-h) on strong turn and100-h on weak turn, retaining the same
incoming history. It fixes the equality-at100/high-clock-mate boundary and
returns immediately to the full comparison. No standalone freeze is planned.

Exact remaining step: evaluate the fixed-barrier geometric mate condition by
compact analytic regions with matching lower bounds against ALL strong choices.
A renaming of that condition, its finite search recurrence or another sufficient
wall policy would not complete the claim. No further foundation is automatically
admitted. Full FIDE correspondence and exact global WDL/DTZ are still OPEN.

## Primary-source triage (no oracle data used)

[Thanatipanonda, How to Beat Capablanca (2006)](https://arxiv.org/html/math/0606251v1)
gives an analytic optimum for a specified corner-aligned initial family on
rectangular boards. It is not an arbitrary-position or incoming-history formula;
formalising that isolated family would not discharge this direct obligation.

[Thanatipanonda, Rook Endgame Problems in m by n Chess (2014)](https://arxiv.org/abs/1403.4966)
states a proved bound for narrow boards and a conjectural general rectangular
bound in its abstract. The general assertion cannot be imported as a theorem,
and neither statement supplies the needed rule-aware history classification.
Only primary analytic-paper pages were opened; no tablebase, stored outcomes,
engine or per-position value certificates were consulted. This source check
rejects an unjustified shortcut, not the full KRK target.

Return/completion criterion: establish the explicit whole-domain criterion and
its upper AND lower strategy arguments, with necessary model correspondence;
then audit and formalise that result. Until then the positive-clock/history,
full FIDE and exact-distance obligations remain OPEN. No KQK work is authorised.
