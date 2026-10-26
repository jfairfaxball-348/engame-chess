# Current work — KRK (live bookmark, not a session gate)

**Status:** KRK OPEN; active research resumed by the owner. Continue a sustained attack without session ceremonies or freezing milestones. Preserve existing proof evidence and check new mathematics locally.

**Objective:** Prove and formalise a compact, explicitly evaluated outcome/strategy criterion for **every admitted KRK history with positive halfmove clock**, both sides to move, both colours, all legal terminal cases and relevant current/intended draw claims. Stay with the hardest open quantified obligation; do not replace it with a collection of sufficient special cases.

**Immediate mathematical gap:** The [fixed-incoming-key-barrier paper reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) is not yet a closed geometric result. Evaluate that barrier condition analytically with explicit regions **and matching defender lower bounds against every strong-side legal alternative**. Integrate the deadline max(1,100-h) on strong turns and 100-h on weak turns, including original incoming history, legal rook captures and root/mate exceptions. The deadline lemma EC-C053 has passed local Lean checks but is not frozen. The reduction is paper-only, not Lean-formalised.

**Current analytic entry points:** [terminal geometry](proofs/KRK_MATE_GEOMETRY.md), [complete immediate-mate formula](proofs/KRK_MATING_MOVES.md), [edge-depth lower bound](proofs/KRK_EDGE_DEPTH_LOWER_BOUND.md), and [last-defender-reply classification](proofs/KRK_LAST_REPLY.md). The immediate formula evaluates ongoing strong h>=98. The last-reply formula evaluates ongoing weak h>=97, retaining current/intended claims and proving exact two-ply distance on its winning region. The depth bound proves holding whenever h+2d+(3 on strong / 2 on weak)>100 and d>0. Next evaluate the preceding strong move into the explicit last-reply regions, with incoming-key barriers and all legal alternatives retained. These results do not settle the remaining barrier game.

**Then:** Establish full FIDE-rule correspondence for the actual history/claims model and exact global WDL/DTZ distance semantics. A clock-free strategy, generic game recurrence, per-position certificates or an upper bound alone does not settle these obligations.

**Trusted starting point:** 48 frozen theorem bundles through EC-T0048 in [the ledger](theorems/LEDGER.csv). EC-T0048 certifies all-wall93, legal strong arrivals97, weak forcing98 and the both-turn RAW clock-zero win criterion. These are partial KRK results, not full outcome/distance parity. Historic S092 details live in [the frontier](research/KRK_POSITIVE_CLOCK_FRONTIER.md), [the proof](proofs/KRK_EXACT_CLOCK_DEADLINE_S092.md) and existing evidence.

**Working method:** Focus on the direct missing proof; run relevant Lean checks, commit meaningful source, and continue across mathematical milestones. No new session reports, freeze exercise or approval ceremony. Update this page only when the actual mathematical direction changes.

**Next material class:** KQK only after KRK closure and owner direction.
