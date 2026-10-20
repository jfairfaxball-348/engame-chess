# S066 — Conditional sufficient-budget raw lifting Gate F

Own proof source `7155c3424a5e315ea758f916d939b6696e0da261`; NEW GitHub clone `/workspace/engame-chess/work/s066-gate-f`, .lake absent before build. Full 92-job build exit 0 (780.499s); complete AxiomCheck exit 0 at 2026-10-20T15:10:49Z, 287 allowed reports. Exact main AND helper inspected, standard-three only; entire working/clean runner and all formal bytes identical.

For EVERY admitted raw s/colour/n, clock-free MateWithin at n plus strict
clock(s.val.trace)+n<100 and count<3 on EVERY actual raw prefix through n imply
raw-layer RuleMateWithin at SAME n. New actual-step prepend helper retains exact
raw traces and depth. Induction: zero/early mate Goal; otherwise nondead/legal
successor/root bounds give ongoing, ALL intended children below100/3 exclude all
raw thresholds, child clock/count certificates descend by append bound/prepend,
strong chosen child and ALL weak replies/nonempty retained. No child-ongoing
filter. Recursive witnesses used directly, no extra tree extraction assumed.

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

Conservative SUFFICIENT all-raw-prefix certificate, not necessity or a certificate
on any general KRK history. It bounds continuations outside the chosen strategy,
including raw paths after terminals; strategy-specific repetition certificates
and numerical KRK bounds still needed. Failure gives no draw theorem. No full
FIDE key/rights/history/adjudication/real claim correspondence or complete KRK
outcome/strategy/distance/WDL/DTZ/initial value. Transparent same-agent separate
paper/Lean audit, not independent external review. Symbolic zero/early mate,
99/100,2/3,current/intended/new-child-key,zeroing,adverse capture-to-KK,exact history,
all colours/promotions/raw flags; no full-game run/enumeration/oracle/per-position
certificates/novelty. Latest owner instruction: finish/close S066, then STOP before S067. KRK remains incomplete.

Reproduce: `python sessions/evidence/S066/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE 7155c3424a5e315ea758f916d939b6696e0da261`.
Validate: `python sessions/evidence/S066/validate.py`.
