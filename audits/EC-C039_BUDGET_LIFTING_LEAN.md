# EC-C039 — Conditional raw lifting fidelity audit

S066, same-agent review, not independent external audit. Standalone paper and
separate adversarial audit completed before Lean. New Prepend and BudgetLifting
modules, no frozen source edits. Exact helper retains actual states and step;
main theorem quantifies every admitted s/colour/n, strict clock+n<100 and EVERY
raw prefix through n with count<3, giving SAME-budget raw RuleMateWithin from
clock-free MateWithin. No hypothesis weakened to a root count or erased path.

Helper inducts on actual Extends and prepends the same step. Main inducts on n:
zero/early mate directly Goal; otherwise clock-free nondeadness/legal-move
existence and root bounds give ongoing. Depth1 actual intended-child bounds
exclude ALL current/intended raw thresholds. Exact prepend and append clock
bound descend safety to EVERY actual child. Strong chosen move retains actual
m/hm and admitted append; weak nonempty replies and ALL admitted steps retained,
with raw soundness supplying clock-free continuation. No child-ongoing test.
No finite-tree extraction assumed: recursive witnesses used directly.

One retained initial authoring failure in Prepend: Lean's induction hypothesis
was generalised over the leading step proof, so it required `ih step` rather than
`ih`. Supplied that argument; statement/model unchanged. Logs/commands/exits/UTC
retained as authoring-failure-01. Working build/complete runner then passed.
Gate F passed after the retained authoring fix.

Own proof source `7155c3424a5e315ea758f916d939b6696e0da261`; NEW GitHub clone `/workspace/engame-chess/work/s066-gate-f`, .lake absent before build. Full 92-job build exit 0 (780.499s); complete AxiomCheck exit 0 at 2026-10-20T15:10:49Z, 287 allowed reports. Exact main AND helper inspected, standard-three only; entire working/clean runner and all formal bytes identical.

Standalone precise paper/separate adversarial audit BEFORE Lean, then LOCAL_VERIFIED.
Initial Prepend authoring failure retained: induction generalised the leading
step proof, so use ih step rather than ih. Statement/model unchanged. Failure
log/commands/exits/times/UTC retained; working incremental build/full runner then
passed. One new fresh Gate F build, no fresh-build failure/interruption/retry.
Full logs/commands/exits/times/UTC, executable/toolchain, clean HEAD/tree/status,
all source/transitive SHA256 retained. Official core Lean4.35.0 release
eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim/TLS/checksum changes.
Inherited proxy/CA, current unrestricted/enforced policy. Hosted CI unobserved.
Relevant ledger tests/structure/evidence/preservation/full-table/full-prompt/
local-link/diff checks passed, prior protected files/36 ledger rows unchanged,
aggregates/runner additive. No unrelated diagnostics/trivial tests. Gate Z separate.

Strong sufficient all-raw-prefix certificate, not necessity, certificate existence
on any particular KRK history, numerical bound, rule-aware outcome/distance or
full FIDE correspondence. Both colours/promotions/raw flags,99/100,2/3,zeroing,
actual intended/new-key counts and adverse terminal children checked symbolically.
No full-game run/enumeration/oracle/per-position certificates/novelty.
