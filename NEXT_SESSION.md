# Current work — KRK (live bookmark, not a session gate)

**Status:** KRK OPEN. Research was last stopped at the owner's request after S092; work can resume in an ordinary local work period or upon the next 'run next session' request. No numbered session, closeout, report or rewritten prompt is required.

**Objective:** Prove and formalise a compact, explicitly evaluated outcome/strategy criterion for **every admitted KRK history with positive halfmove clock**, both sides to move, both colours, all legal terminal cases and relevant current/intended draw claims. Stay with the hardest open quantified obligation; do not replace it with a collection of sufficient special cases.

**Immediate mathematical gap:** The [fixed-incoming-key-barrier paper reduction](proofs/KRK_STATIC_HISTORY_REDUCTION_S092.md) is not yet a closed geometric result. Evaluate that barrier condition analytically with explicit regions **and matching defender lower bounds against every strong-side legal alternative**. Integrate the deadline max(1,100-h) on strong turns and 100-h on weak turns, including original incoming history, legal rook captures and root/mate exceptions. The deadline lemma EC-C053 has passed local Lean checks but is not frozen. The reduction is paper-only, not Lean-formalised.

**Then:** Establish full FIDE-rule correspondence for the actual history/claims model and exact global WDL/DTZ distance semantics; verify and freeze completed claims using [the minimal proof standard](docs/PROOF_PROTOCOL.md). A clock-free strategy, generic game recurrence, per-position certificates or an upper bound alone does not settle these obligations.

**Trusted starting point:** 48 frozen theorem bundles through EC-T0048 in [the ledger](theorems/LEDGER.csv). EC-T0048 certifies all-wall93, legal strong arrivals97, weak forcing98 and the both-turn RAW clock-zero win criterion. These are partial KRK results, not full outcome/distance parity. Historic S092 details live in [the frontier](research/KRK_POSITIVE_CLOCK_FRONTIER.md), [the proof](proofs/KRK_EXACT_CLOCK_DEADLINE_S092.md) and existing evidence.

**Working method:** Focus on the direct missing proof; run tests and Lean checks when warranted, commit meaningful source or finished mathematics, freeze only verified theorems. Keep working across multiple milestones without creating `sessions/S094...` files or end-of-session tables. Update this page only when the actual next obligation changes.

**Next material class:** KQK only after KRK closure and owner direction.
