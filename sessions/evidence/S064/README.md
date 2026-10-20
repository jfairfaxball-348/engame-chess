# S064 — Concrete RAW stopped-history Layer Gate F

Own proof source `e346ebccd93971887cb3017487ecd1efff1bf51e`; NEW GitHub clone `/workspace/engame-chess/work/s064-gate-f`, .lake absent before build. Full 90-job build exit 0 (630.829s); complete AxiomCheck exit 0 at 2026-10-20T14:42:59Z, 285 allowed reports. Exact main inspected, standard-three only; entire working/clean runner output and all formal bytes identical.

NEW RawHistoryLayer.State retains actual raw state/entire indexed trace and
StoppedHistory.Admissible proof. Erase underlying endpoint, BoardStep actual
RawBoardStep, Ongoing raw classify=ongoing, CanClaim raw AvailableThreshold.
Concrete Layer soundness from raw_step_sound; EVERY Legal reply lifted using
admissible ongoing parent and EC-T0035, retaining terminal children; nondeadness
from ongoing_iff. Main raw_ruleMateWithin_project instantiates frozen generic
projection with EXACT SAME s/colour/n. No certificate existence or converse.

Standalone paper and separate adversarial audit completed before Lean, then
LOCAL_VERIFIED. New shared definitions and one main module, additive aggregates/
runner, all prior frozen sources untouched. Working incremental build and complete
runner passed first attempt. One new GitHub Gate F build, no failure/interruption/
retry. Full logs/commands/exits/times/UTC, executable/toolchain identity, all source/
transitive SHA256 and clean HEAD/tree/status retained. Official core Lean4.35.0
release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim/TLS/checksum
changes. Inherited proxy/CA, current unrestricted/enforced network policy.
Hosted CI unobserved. Relevant ledger tests/structure/evidence/preservation/full
progress table/prompt/local-link/diff checks passed; prior protected files and35
ledger rows unchanged. No unrelated diagnostics/trivial tests. Gate Z separate.

Concrete RAW Layer only; no full FIDE key/rights-history/adjudication/real claim
protocol correspondence. No rule-aware KRK outcome/strategy, numeric bound,
holding/determinacy, WDL/DTZ or initial value. Same-agent separate paper/Lean audit,
not independent external review. Start/current terminal/parent terminal/terminal
child, subtype witness and all legal moves/colours/promotions/raw flags and zero
budget reviewed symbolically. Optional claim opportunities separate; no successful/
invalid claim/procedural phase in traces. No full-game run/enumeration/oracle/
per-position certificates/novelty. Owner scope remains finish KRK/freeze, stop KQK.

Reproduce: `python sessions/evidence/S064/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE e346ebccd93971887cb3017487ecd1efff1bf51e`.
Validate: `python sessions/evidence/S064/validate.py`.
