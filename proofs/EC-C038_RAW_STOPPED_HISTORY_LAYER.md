# EC-C038 — Concrete raw stopped-history Layer and same-budget projection

S064, 2026-10-20. Classical interface instantiation, no novelty claim.

## Definitions and exact claim

Use a NEW RawHistoryLayer.State := {s : RawTrace.State //
StoppedHistory.Admissible s.trace}. The subtype retains the ENTIRE actual stored
initial-rooted indexed trace plus an admissibility proof; it does not replace
it with a board or a clock/count vector. Define erase := RawTrace.erase of the
underlying state, BoardStep := RawBoardStep on the two underlying states,
Ongoing := RawAdjudication.classify underlying = ongoing, and CanClaim :=
RawClaims.AvailableThreshold underlying. A NEW concrete RAW HistoryLayer.Layer
has precisely these fields and the three interface proofs below.

For EVERY admitted state s, colour σ and natural ply budget n, prove:
HistoryLayer.RuleMateWithin layer σ n s → MateWithin σ n (erase s).
The budget n is unchanged. This is a conditional certificate projection, not
existence of a winning certificate, a converse or a numerical KRK bound.

## Complete paper argument before Lean

Soundness: a BoardStep is an actual RawBoardStep. Frozen raw_step_sound gives
Legal at the two erased endpoints; the extra ongoing hypothesis need not be
used to weaken or replace raw legality.

Full replies: let s be ongoing and let r be ANY Legal successor of erase s.
The subtype supplies Admissible s.val.trace; S062/S063's full reply conjunct,
with this proof and ongoing, produces raw t, Admissible t.trace, actual
RawBoardStep s.val t and exact erase t=r. Choose subtype child ⟨t,admissible⟩.
This supplies BoardStep and exact erasure, including a child whose status is
mate or draw. The construction NEVER assumes child ongoing.

Ongoing nondeadness: the first component of frozen RawAdjudication.ongoing_iff
applied to the underlying state proves ¬DeadK at the erased endpoint.
These prove EVERY field of the frozen abstract Layer interface for the exact
chosen functions. The frozen generic ruleMateWithin_project then gives the
stated same-budget conclusion, using this concrete layer. No new induction or
unverified strategy transport is hidden in the instantiation.

## Boundary and rules scope

Start is admitted by the stopped-history definition without assuming an initial
ongoing theorem. The current endpoint can be terminal. Any actual BoardStep
between admitted states forces its parent ongoing by the stopped-history append
guard, even though BoardStep's definition does not add a new classifier filter.
A terminal child is retained; a terminal parent has no admitted next board step.
Subtype proof witnesses do not alter the underlying history or Legal witness.
All colours, promotions and kernel flags are covered by the general proofs.

CanClaim records current/intended raw 100/3 availability as a separate predicate.
It may hold at a raw terminal state, but RuleMateWithin tests actual Goal first,
and only its ongoing branch offers play or tests defending claim availability.
Optional claims may be declined; successful/invalid claims and procedural phases
are not BoardSteps. No assertion about real claim validity is introduced by naming
the interface field CanClaim. The existing raw predicate's scope is unchanged.

This is a concrete RAW layer relative to the chosen classifier/thresholds.
Initial-rooted trace flags are retained, but no new FIDE castling-rights/key or
adjudication/claim-protocol correspondence is proved. No full FIDE Layer, winning
certificate existence, converse strategy lifting, rule-aware KRK outcome, numeric
distance, holding/determinacy, WDL/DTZ or initial-position value follows.
Sources: frozen EC-T0020 abstract interface/projection, EC-T0021 raw trace
soundness, EC-T0034 ongoing guards, EC-T0035 stopped-history full replies, raw
claim definitions and S032 §2/4/5. No new external retrieval, full-game diagnostic,
enumeration, engine/tablebase oracle or per-position certificates.
