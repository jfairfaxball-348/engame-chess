# S044 — Lean fidelity review of EC-C028

Same-agent review, not independent external review. Paper/adversarial audit saved
BEFORE Lean. Official core Lean4.35.0, no new dependency.

RawRepetition/Definitions defines LegalEP as actual isLegal=true plus frozen
RawClock.Pawn, exact raw ep/destination equality, distinct files, empty landing
square and opposing flank pawn. It matches the named existing CaptureEvent EP
branch with legality required; play's epCapture is local, not imported as an
exported predicate. No pseudo-legal substitute, count seed, terminal or material/
colour/strategy filter. effectiveEP is explicitly NONCOMPUTABLE classical
existence-filtered q.ep, not executable search or enumeration.

One main EffectiveEP/effectiveEP_spec gives both none↔no legal event and
some dst↔actual legal event targeting dst. Availability case selects a witness;
its flag proves q.ep is SOME and destination consistency by Option.some.inj.
Reverse direction uses the event's exact flag. No-availability case reduces to
none and rules out an existential. No endpoint target consistency assumed.
Both colours/arbitrary raw flags covered; lawful history not certified.

Initial compile failed after existential unpacking cleared `available` while
later steps referred to it; explicitly reconstructing its actual witness fixed
the proof. A redundant simpa warning was resolved by contradiction simplification.
Full initial failure retained; no mathematical definition/statement weakened.
Final incremental build passed (73 jobs), complete AxiomCheck exit 0, no warnings.
Exact definitions/combined statement printed; main standard-three only.
Symbolic pin/no-pawn/flag/wrong-kind/occupied/flank/multiple-source controls only,
no concrete pinned board or compatible full promotion/ep/castling/threshold game
constructed/run. No full repetition key, FIDE claims/adjudication or KRK distance.
Gate F pending until published exact-source fresh verification.

## Completed Gate F

Own published source `28bdacfa34995ed3d778bfb2dab1654e46999f0c`; ONE NEW GitHub clone with no .lake
before build. Full 73-job lake build exit 0, 417.929s; COMPLETE AxiomCheck
exit 0 at 2026-10-20T08:44:40Z, 275 allowed reports, main standard-three only.
Definitions/combined statement inspected; working/clean outputs identical.
Every formal source matches own exact anchor, all source/transitive hashes and
clean HEAD/tree/status retained. Two new modules forbidden scan zero. Official
core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/
shim. Initial local failed log retained; fresh build passed without warning or
failure. Gate F complete, Gate Z pending. Hosted CI unobserved.
