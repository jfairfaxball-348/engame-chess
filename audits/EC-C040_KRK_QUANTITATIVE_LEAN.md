# EC-C040 — Lean fidelity review (S068)

Separate same-agent review; not independent external review. The standalone S067
paper and adversarial paper audit preceded all S068 Lean work. Classical geometry;
no novelty, tablebase, engine, exhaustive-class or per-position-certificate claim.

The new Rules/KRKBound modules formalise exactly the paper's clock-free 508-ply
claim. Arrival quantifies both colours/all flags, exact IsKRK, strong turn and a
legal incoming move. The stronger NotCheck result uses no weak check instead of
arrival. PositiveSetup handles the chosen positive frame. All canonical noRights
sources are explicit; Bound.Transport preserves the supplied MateWithin n by
induction. It does not assert unrestricted raw-position symmetry or optimality.

Fixed-budget Choose/Defend/Pair construct the frozen recurrence at n+1/n+2.
Existing existential ForceMate constructors are used ONLY to derive the nondeadness
guard, never to assign the numerical budget. The supplied fixed-budget successors
remain verbatim in the new recurrence. Every defender node has a nonempty legal
reply witness and every legal reply is retained, including terminal branches.

Pursuit uses the frozen symbolic legal-action geometry. Its local good, wide and
offset-one branches pay 2, 6 and 8 plies respectively before exit or smaller
oriented-file induction. The declared result is 8*(7−pursuitFile d sk)+E. LowerBand
pads both physical orientations to 56+E; aligned files use the exit budget directly.
Definitions.LowerExitBound gives the same E to EVERY admissible exit.

Wall uses outer rank induction and inner gap induction. Inner budget is
84*(n−1)+62+4*(g−1), ready budget is smaller by two. Normalization costs two at
every gap call. Upper advance/rescue pays four, including the briefly threatened
strong-turn rook branch. Aligned edge mate uses the explicit zero-budget goal;
nonedge replies have a strictly higher wall. Impossible boundary cases discharge
by geometric inequalities (omega), not by a fictitious U(0) winning wall. Gap≤6
pads the inner result to 84*n. WallCeiling pads rank≥1 to 504.

Entry/ClearEntry/axis entry add at most two to 504. OffRank adds at most two more
to 506, including axis switching after reduced vertical separation. SameRank
retreat and protected entry use 506; BackRank preparation gives 508. PositiveSetup
pads all branches to 508; NotCheck uses same-budget transport and Arrival uses
actual legal-mover safety. Safety/nonempty facts are actual kernel lemmas.
Legal rook captures to KK are excluded only by the proved safety hypotheses at
weak nodes, not removed from legal reply sets. Unchosen strong moves are irrelevant.

All added main declarations have separate modules; shared exit definition is in
Definitions. Public geometry/composition helpers are included in AxiomCheck along
with every main declaration. Adapted private helpers retain complete proof source
in their containing modules. Frozen files are unchanged. Axiom/clean-build outcome
is recorded in sessions/evidence/S068 only when observed; this audit alone does
not promote status. Authoring failures and actual repairs are retained there.

The 508 ceiling exceeds 100, so it gives no strict clock+n<100 KRK certificate.
No normalized-key uniqueness, incoming-history certificate, holding strategy,
complete FIDE outcome, optimal distance or WDL/DTZ parity follows. Gates F/Z and
rule-aware coverage are kept separate.
