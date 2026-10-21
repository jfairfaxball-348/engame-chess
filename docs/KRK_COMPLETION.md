# Short-term roadmap: direct attack on KRK closure

Current owner direction (2026-10-21): resume consecutive KRK sessions until closure, superseding the S076 pause. Stop before KQK.

Owner direction, 2026-10-20: KRK closure is the research priority across as many
sessions as needed. Owner explicitly resumed on 2026-10-21: run the next session
and keep going until KRK is closed. Stop before KQK.

## Evidence and completion standard

KRK dead/live and clock-free forcing classification are frozen. The concrete RAW
history Layer is frozen as EC-T0036. EC-C039's conditional lifting is formally
verified at proof source `7155c3424a5e315ea758f916d939b6696e0da261`, awaiting
Gate Z. There are 46 frozen bundles after S085, including universal RAW termination;
complete material-class coverage remains open.

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

S069: EC-C040 frozen as [EC-T0037](../theorems/frozen/EC-T0037/v1.md) after a new own-source Gate Z. Milestone A has a certified explicit ceiling; milestone B is next. 37 bundles, no new rule-aware covered inputs. S070 attacks a minimal-rank strategy with all-defence normalized-key nonrepetition; incoming history remains separate.

S070: EC-C041 FORMAL_VERIFIED, [key-simple minimal-budget strategy](../proofs/EC-C041_KRK_STRATEGY_REPETITION.md). Every weak legal reply retained; full-line pairwise raw keys and ≤508-ply root ceiling. Gate Z pending. Milestone B now returns to actual incoming-history counts and raw rule-layer lifting; no rule-aware input family certified yet.

S071: EC-C042 FORMAL_VERIFIED, [actual-history rank-policy lifting and conditional84-ply RAW rank-six wall family](../proofs/EC-C042_KRK_STRATEGY_HISTORY.md). Supplied clock/current count and static incoming lower-winning-rank histogram remain explicit; all weak executed/intended replies retained. Partial RAW input coverage only, full FIDE/outcome/holding/distances open. S072 freezes own sources for EC-C041/042 before returning to direct quantitative coverage.

S072: [EC-T0038](../theorems/frozen/EC-T0038/v1.md) and [EC-T0039](../theorems/frozen/EC-T0039/v1.md) freeze the key-simple strategy and actual-history conditional84-ply RAW wall family at their separate own sources. S073 returns to sharper numerical wall/pursuit costs and clock coverage; complete FIDE/outcome/holding/distance obligations stay open.

S073: EC-C043 FORMAL_VERIFIED, [file/rank-edge credited walls and conditional73-ply RAW frame-wall family](../proofs/EC-C043_KRK_SHARPER_WALL.md), clock≤26 under unchanged incoming conditions. Gate Z pending; global508 arrival bound unchanged. S074 directly proves parametric setup composition before any global442 claim. Full FIDE/outcome/holding/distance obligations remain open.

S074: EC-C044 FORMAL_VERIFIED, [actual parametric setup and global442/443 ceilings](../proofs/EC-C044_KRK_PARAMETRIC_SETUP.md). WallBudget(B)→B+4/B+5 instantiated from proved438; all weak replies/flags retained. No general RAW/FIDE win because bounds exceed100. S075 separate own-source freeze for EC-C043/044, then direct outcome/holding termination attack.

S075: [EC-T0040](../theorems/frozen/EC-T0040/v1.md) and [EC-T0041](../theorems/frozen/EC-T0041/v1.md) separately freeze sharper73 walls/conditional RAW family and global442/443 actual setup. Direct next obligation is all-flag KRK material/quiet-step and admitted clock-bounded termination toward outcomes/holding. No full FIDE/class/distance closure.

S076: EC-C045 FORMAL_VERIFIED. Universal admitted RAW KRK termination formally verified: every ongoing root of clock h has at most150−h board plies, terminal roots0; both turns/colours/all flags/every legal move including castling and terminal rook capture. [Evidence](../sessions/evidence/S076/README.md). 41 frozen bundles; Gate Z pending. Complete RAW holding/outcomes, full FIDE correspondence and exact WDL/DTZ remain open. Owner requested STOP after S076; S077 is saved and paused, requiring explicit resumption.

S077: S077 froze universal admitted RAW KRK termination as EC-T0042 after separate own-source Gate Z; 42 bundles. Complete RAW holding/outcomes, full FIDE correspondence and exact WDL/DTZ remain open. Owner resumed consecutive KRK sessions until closure; stop before KQK. [EC-T0042](../theorems/frozen/EC-T0042/v1.md). S078 attacks genuine all-history RAW holding policies.

S078 formally verified actual legal all-history RAW KRK holding policies iff opponent nonforcing, plus bounded stopped compliant play.42 bundles remain frozen; geometric outcome characterisation, full FIDE correspondence and exact WDL/DTZ remain open. [Paper](../proofs/EC-C046_KRK_HOLDING.md).

S079 froze actual all-history RAW KRK holding duality and bounded stopped policy play as EC-T0043;43 bundles. Mathematical coverage is unchanged from S078; geometric outcomes, full FIDE correspondence and exact WDL/DTZ remain open. [EC-T0043](../theorems/frozen/EC-T0043/v1.md).

S080 formally verified universal strong RAW holding/weak nonforcing, exact ongoing high-clock criteria (weak h>=99; strong h>=98 iff immediate mate), and exact one-ply budget on those wins.43 bundles remain frozen; low-clock geometry, actual winning-policy bridge, full FIDE and global WDL/DTZ remain open. [Paper](../proofs/EC-C047_KRK_HIGH_CLOCK.md).

S081 froze universal strong RAW nonloss, exact high-clock forcing criteria and local optimal one-ply budget as EC-T0044;44 bundles. Mathematical coverage unchanged from S080; low-clock geometry, actual winning-policy bridge, full FIDE and global WDL/DTZ remain open. [EC-T0044](../theorems/frozen/EC-T0044/v1.md).

S082 formally verified independent actual bounded winning policies iff full RAW forcing on every admitted KRK history, exact same-B certificate extraction and actual terminal mate continuations.44 bundles frozen; geometric low-clock coverage, full FIDE and global exact WDL/DTZ remain open. [Paper](../proofs/EC-C048_KRK_WINNING_POLICY.md).

S083 froze independent actual bounded RAW winning-policy correspondence, exact B certificate extraction and actual terminal mate continuation as EC-T0045;45 bundles. Mathematical coverage unchanged from S082; low-clock geometry/full FIDE/global exact WDL-DTZ remain open. [EC-T0045](../theorems/frozen/EC-T0045/v1.md).

S084 formally verified automatic KRK incoming-count control at nondead clock0 and same-budget lifting of any supplied N<100 certificate; framed rank-six clock0 walls now have RAW W73/actual win without incoming premises.45 bundles frozen; full low-clock geometry/FIDE/global exact WDL-DTZ remain open. [Paper](../proofs/EC-C049_KRK_FRESH_HISTORY.md).

S085 froze clock-zero KRK count control, incoming-premise-free supplied-budget lift and concrete73 framed-wall actual wins as EC-T0046;46 bundles. Mathematical coverage unchanged from S084; complete low-clock/history outcomes, full FIDE and global exact WDL-DTZ remain open. [EC-T0046](../theorems/frozen/EC-T0046/v1.md).
