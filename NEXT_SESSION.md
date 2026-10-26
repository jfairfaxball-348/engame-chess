# Current work — KRK (live bookmark, not a session gate)

**Status:** KRK OPEN; active research resumed by the owner. Continue a sustained attack without session ceremonies or freezing milestones. Preserve existing proof evidence and check new mathematics locally.

**Objective:** Prove and formalise a compact, explicitly evaluated outcome/strategy criterion for **every admitted KRK history with positive halfmove clock**, both sides to move, both colours, all legal terminal cases and relevant current/intended draw claims. Stay with the hardest open quantified obligation; do not replace it with a collection of sufficient special cases.

**Immediate mathematical gap:** The [fixed-incoming-key-barrier paper reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) is not yet a closed geometric result. Evaluate that barrier condition analytically with explicit regions **and matching defender lower bounds against every strong-side legal alternative**. Integrate the deadline max(1,100-h) on strong turns and 100-h on weak turns, including original incoming history, legal rook captures and root/mate exceptions. The deadline lemma EC-C053 has passed local Lean checks but is not frozen. The reduction is paper-only, not Lean-formalised.

**Current analytic entry points:** [terminal geometry](proofs/KRK_MATE_GEOMETRY.md), [immediate mate](proofs/KRK_MATING_MOVES.md), [edge-depth lower bound](proofs/KRK_EDGE_DEPTH_LOWER_BOUND.md), [last defender reply](proofs/KRK_LAST_REPLY.md), and [three-ply incoming-key barriers](proofs/KRK_THREE_PLY_BARRIERS.md). Checked formulas evaluate ongoing weak h>=97 and strong h>=96, including all legal alternatives, the original trace and exact winning distances 2 / (1 or 3). Nonmating strong entries use two explicit original-key counts below two. The depth bound gives additional holding regions at lower clocks. The next uncovered clock band is weak h=95/96 and strong h=94/95; pursue geometric evaluation rather than a generic recurrence. The full barrier game remains open.

**Then:** Establish full FIDE-rule correspondence for the actual history/claims model and exact global WDL/DTZ distance semantics. A clock-free strategy, generic game recurrence, per-position certificates or an upper bound alone does not settle these obligations.

**Trusted starting point:** 48 frozen theorem bundles through EC-T0048 in [the ledger](theorems/LEDGER.csv). EC-T0048 certifies all-wall93, legal strong arrivals97, weak forcing98 and the both-turn RAW clock-zero win criterion. These are partial KRK results, not full outcome/distance parity. Historic S092 details live in [the frontier](research/KRK_POSITIVE_CLOCK_FRONTIER.md), [the proof](proofs/KRK_EXACT_CLOCK_DEADLINE_S092.md) and existing evidence.

**Working method:** Focus on the direct missing proof; run relevant Lean checks, commit meaningful source, and continue across mathematical milestones. No new session reports, freeze exercise or approval ceremony. Update this page only when the actual mathematical direction changes.

**Next material class:** KQK only after KRK closure and owner direction.
