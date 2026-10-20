# Short-term roadmap: direct attack on KRK closure

Owner direction, 2026-10-20: KRK closure is the research priority across as many
sessions as needed. Owner subsequently resumed research and explicitly requested consecutive
sessions until asked to stop. Stop before KQK.

## Evidence and completion standard

KRK dead/live and clock-free forcing classification are frozen. The concrete RAW
history Layer is frozen as EC-T0036. EC-C039's conditional lifting is formally
verified at proof source `7155c3424a5e315ea758f916d939b6696e0da261`, awaiting
Gate Z. There are 36 frozen bundles; material-class coverage is unchanged.

Closure means complete rule-aware KRK outcomes/strategies and the project's
specified distance correctness, with all necessary results verified and frozen.
An existential clock-free mate proof, a conditional winning family, a raw Layer,
a mate upper bound, or a bundle count alone does not establish closure. The
[S032 specification](../research/KRK_RULE_DISTANCE_SPEC.md) and
[project roadmap](ROADMAP.md) retain the L1–L4 and WDL/DTZ obligations.

## Ordered attack

Milestones are proof obligations, not one-session promises. Carry an unfinished
main obligation across sessions rather than replacing it with easier library work.

| Priority | Direct KRK obligation | Evidence needed to advance |
|---|---|---|
| A — Quantitative winning strategy | Turn the frozen safe-setup/wall/pursuit strategy into an explicit geometric ply bound for every legal strong-turn KRK arrival, both colours and arbitrary kernel flags; preserve EVERY defensive reply. | Standalone paper, adversarial audit, and then Lean proof of a stated bound `B(q)` and a proved numerical ceiling. Derive the numbers from the argument; an existential `ForceMate` witness is insufficient. Expose setup, tempo, pursuit and rank-advance costs. |
| B — Strategy and history safety | Control repetitions on the chosen winning strategy and ALL defensive branches, and connect the usable bound to actual clock/history inputs and FIDE semantics. | Proved progress/no-cycle invariant or another exact strategy certificate; account separately for earlier history counts, current and intended claims, resets and mate/draw precedence. Prove each rights/key/adjudication bridge actually needed. State the precise input family for each rule-aware winning corollary. |
| C — Complete outcome coverage | Cover both turns and EVERY admissible KRK history, including those outside sufficient winning conditions. | Necessary-and-sufficient win/draw classification with holding/termination arguments where needed; include immediate mate, dead/stalemate, legal rook captures to KK, high clocks, repetitions and claims. Failure of a sufficient certificate is not a draw proof. No raw-to-FIDE correspondence gap may be hidden. |
| D — Correct distances | Prove the project's rule-aware distance target and optimality/convention correspondence on the complete covered domain. | Exact minimax/optimality arguments and the relevant 50-move WDL/DTZ semantics. Source convention definitions without consulting tablebase outcomes. A nonoptimal mate upper bound is an intermediate result, not exact DTM/DTZ parity. |
| E — Freeze and closure audit | Complete the existing proof/audit/Lean/freeze gates and check every remaining KRK obligation against actual evidence. | Immutable exact-source manifests, observed builds/axioms, full input coverage and an explicit closure checklist. Only then mark KRK complete. Do not begin KQK under the current direction. |

A and B may need refinement together. A large proved bound is genuine partial
progress, but if it cannot support the relevant clock cases, improve it or state
that limitation. Neither an invented sub-100 bound nor a clock-only criterion
settles history-dependent outcomes. A strategy that creates no new repetition
may still encounter keys already present in the incoming history.

## Current direct attack: EC-C040

S067: EC-C040 is LOCAL_VERIFIED on paper, with a 508-ply global ceiling,
84*(7−rookRank) wall ceiling, ≤56-ply lower pursuit before a bounded exit, and
≤4-ply setup. Separate same-agent audit completed; no Lean/build/freeze yet.
[Paper](../proofs/EC-C040_KRK_QUANTITATIVE_BOUND.md). S068 formalises this exact
statement. The coarse ceiling exceeds 100 and does not certify history safety.
Material-class/rule-aware coverage and 36 frozen bundles are unchanged.

Principal target remains the quantitative KRK strategy in A, beginning with a paper proof
and separate adversarial audit. Read the existing KRK safe-setup, wall, lower-band
pursuit and rank-advance arguments; make their costs and quantified continuations
explicit. Choose one well-posed quantitative claim and carry it through the
normal gates when its argument closes. Do not assume a classical numerical
maximum without proving it in this kernel.

If the full claim does not close in one session, retain the attempted bound,
precise failed inequality/lemma, exact uncovered positions or input family, and
next KRK-specific proof obligation. An incomplete attempt is a valid closeout;
replacing it with an unrelated easy theorem is not. A partial family must remain
labelled partial, with its path to full coverage stated.

## Prerequisite admission and session discipline

Before diverting to a generic/history lemma, record all of:

1. The exact KRK theorem and proof step currently blocked.
2. Why the existing frozen/formal results cannot discharge that step.
3. The smallest missing statement, and the precise coverage or distance obligation it unlocks.
4. An exit criterion for returning to the main attack. Reassess at the next closeout;
   do not automatically extend the detour into another prerequisite sequence.

Dependencies may be necessary, but they are subordinate to an active KRK proof.
The generic mated-key uniqueness idea and stronger generic lifting machinery are
not default next tasks. EC-C039's all-raw-continuation repetition hypothesis can
exclude useful winning strategies; it is not a substitute for B.

Each research closeout reports the current milestone, exact KRK claim, new input
coverage or quantitative bound, remaining gap, and any justified prerequisite.
Say explicitly when coverage is unchanged. Update the stable progress table;
never report percentages based on theorem counts.

[Proof protocol](PROOF_PROTOCOL.md) remains unchanged. Freeze verified results at
appropriate milestones, with every required exact-source Gate Z check. EC-C039's
freeze remains a recorded backlog item, not the default next research priority.
A freeze-only follow-up must identify the main KRK result/dependency it serves;
completing it returns to the direct attack rather than installing a generic detour.
No theorem is frozen by scheduling it here. No new research, build, freeze or
candidate promotion is authorised by this planning update.

No tablebases, engine oracles, exhaustive class proofs or per-position certificates.
Existing frozen sources/records remain immutable; new proofs use new modules.

## S068 quantitative milestone evidence

EC-C040 FORMAL_VERIFIED at `3a4a543625673383f66de70a8f847e340d820570`: 508-ply strong-turn arrival ceiling, coordinate wall bound and same-budget transport. [Evidence](../sessions/evidence/S068/README.md). S069 separately freezes this direct KRK result, then returns to strategy-specific repetition safety. 508 exceeds100; no additional history-aware inputs or exact distances are covered.
