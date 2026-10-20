# S062 — Stopped-history append/full-reply lifting Gate F

Own proof source `67850895bf6130a1f193c299597cd7d4ac209485`; NEW GitHub clone `/workspace/engame-chess/work/s062-gate-f`, .lake absent before build. Full 88-job build exit 0 (582.973s); complete AxiomCheck exit 0 at 2026-10-20T14:20:50Z, 284 allowed reports. Exact main inspected, standard-three axioms only; entire working/clean runner output and all formal bytes identical.

Admissible recurses on the actual initial-rooted indexed Trace: start True,
snoc requires admissible prior AND the exact parent State classifier ongoing.
The one main theorem combines the EVERY legal m/hm append IFF with EVERY Legal
reply lifting to admissible actual RawBoardStep and exact erased endpoint.
Guard is definitional after State cases; reply proof extracts the actual m/hm
witness and appends it. Terminal current endpoints/children are admitted; no
append after terminal parent. No legal reply is pruned. Optional claim
opportunities may be declined; successful/invalid claims and procedural phases
are absent from board-move traces.

Paper and separate adversarial audit completed before Lean, then LOCAL_VERIFIED.
New definitions/main module, additive aggregate imports/runner; frozen sources
untouched. Working build and complete runner passed first attempt. One new GitHub
Gate F clone, no clean-build retry or failure. Full logs, commands/exits/times/UTC,
clean HEAD/tree/status, executable/toolchain identity, source/transitive SHA256
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependency/shim/TLS/checksum changes. Runtime policy observation state unknown,
executor snapshot unrestricted, inherited proxy/CA sufficient. Hosted CI unobserved.
Relevant ledger tests/structure, evidence, preservation, full progress table/prompt,
local-link and diff checks passed. All prior protected files/34 ledger rows
unchanged. No unrelated diagnostics/trivial tests. Gate Z remains separate.

This is stopped-history bookkeeping relative to the CHOSEN RAW classifier,
not certified full FIDE legal-history/rights-key/adjudication/claim correspondence.
No complete Layer, converse strategy lifting, numerical KRK, holding/outcome,
WDL/DTZ or initial-position value follows. Same-agent separate adversarial audit,
not independent external review. Zero/one-ply, terminal parent/child, exact
trace/hm, every terminal-ending reply, both colours/promotions/raw flags checked
symbolically; no full-game run/enumeration/oracle/certificates/novelty claim.

Reproduce: `python sessions/evidence/S062/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE 67850895bf6130a1f193c299597cd7d4ac209485`.
Validate: `python sessions/evidence/S062/validate.py`.
