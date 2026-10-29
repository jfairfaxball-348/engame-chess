# KRK — current mathematical closure obligations

**Status: OPEN.** The owner requested a verified supporting-results freeze and session closeout; the installed continuation prompt targets full KRK completion. [NEXT_SESSION.md](../NEXT_SESSION.md) is the concise live entry point. This is an obligation list, not a timetable or series of session closeouts.

## Certified baseline
- 48 frozen theorem bundles through [EC-T0048](../theorems/frozen/EC-T0048/v1.md), proved in the pinned Lean model. These establish important partial results, not all KRK WDL/DTZ outcomes.
- EC-T0048 establishes an all-defence uniform wall bound93, strong legal arrivals97, weak forcing98 and the explicit both-turn actual RAW clock-zero winning criterion (strong turn, already mate, or safe rook with legal reply).
- Clock-free KRK dead/live and forcing results are frozen. High-clock and some history interfaces are also verified and frozen. See the exact [frozen ledger](../theorems/LEDGER.csv) for scope. No global distance optimality is claimed.

The EC-T0049 supporting-results bundle evaluates every ongoing RAW strong-turn history at
h>=86 and weak-turn history at h>=85, both colours and all orientations, with
exact winning distances 1/3/5/7/9/11/13 and 2/4/6/8/10/12/14 respectively. See the
[thirteen/fourteen-ply criteria](../proofs/KRK_THIRTEEN_FOURTEEN_PLY_HISTORY.md) and
[complete twelve-ply geometry](../proofs/KRK_GLOBAL_TWELVE_GEOMETRY.md). Lower-clock outcomes and
class-wide model/distance closure remain outstanding. See the [detailed remaining-work report](KRK_REMAINING_WORK.md), [installed finish prompt](KRK_FINISH_PROMPT.md), and [EC-T0049 manifest](../theorems/frozen/EC-T0049/v1.md).

## Direct obligations, in priority order
1. **Complete positive-clock/all-history KRK outcome formula.** An explicitly evaluated compact geometric characterisation over every admitted history, either player to move/colour, every legal rook capture, terminal state, current/intended draw claim and actual incoming history. Include an actual justified policy for winning regions AND matching defender lower bounds for drawn regions. An unevaluated minimax recurrence, a per-position atlas or failure of a chosen sufficient policy cannot close this.
2. **Finish necessary model correspondence.** Connect proved RAW/normalized-key/claim facts to the actual FIDE rule model, preserving mate precedence, optional claims, automatic draws and accurate history semantics.
3. **Exact global rule-aware distances.** Establish the required WDL/DTZ conventions and exact optimal distances, not only upper bounds and selected one-ply optima. Then certify complete class parity.

## Current direct route
The [S092 fixed-barrier paper reduction](../proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) reduces old repeated keys to fixed forbidden barriers with exceptions for root and mate leaves. The least-rank strategy argument is still **paper only**. Its [audit](../audits/KRK_STATIC_HISTORY_REDUCTION_S092_PAPER.md) is same-agent, not independent external review.

[EC-C053 deadline](../proofs/KRK_EXACT_CLOCK_DEADLINE_S092.md) gives the necessary strong-turn max(1,100-h) and weak-turn 100-h budget, retaining original incoming history. Its checked deadline statements are included in EC-T0049; neither the deadline alone nor the paper reduction closes the class. The next missing result is **explicit geometric evaluation of the fixed-barrier mate condition** with matching lower bounds against **all** strong-side alternatives, not another sufficient wall policy or a generic history framework. See [exact frontier](../research/KRK_POSITIVE_CLOCK_FRONTIER.md).

When a full claim is proved: audit the actual proof, formalise in Lean, verify, and freeze under [the minimal protocol](PROOF_PROTOCOL.md). Work through multiple stages in one local work period if useful. No separate freeze-only session, checklist report or per-session update is required.
