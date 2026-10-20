# S058 — Exact raw threshold exclusion Gate F

Own source `c75b3760022717e586a789e47c09c03911a43a56`; NEW GitHub clone `/tmp/engame-s058-gate-f`, no .lake before build. Full 84-job build exit 0, 452.708s; COMPLETE AxiomCheck exit 0 at 2026-10-20T13:36:05Z, 282 allowed reports. Main standard-three; whole working/clean report identical.

Exact IFF for every raw s: no AvailableThreshold iff rootclock<100/rootcount<3
and EVERY actual legal intended child clock<100/NEW endpoint OLD-history query<2.
Forward inject root/child threshold into availability, obtain strict Nat bounds;
frozen current append count+1 yields query<2. Reverse root/ALL child bounds refute
both disjuncts. Exact childclock retained, no sufficient root+1 budget substitution.
All actual Moves/promotions/flags/colours/indexed trace/hm retained. Root bounds
separate; no adverse move pruning/reset truncation/parent-current-query shortcut.

Exact main inspected, full formal bytes match own anchor; full source/transitive
SHA256, clean HEAD/tree/status and full logs/commands/exits/times/UTC/toolchain
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change. New module forbidden scan zero. Initial
incremental unknown by_contra tactic failure retained; core Nat.lt_of_not_ge
resolved unchanged statement. Final incremental 84-job build/full working runner
passed without warnings; clean verification passed once, no repeated clean build.
Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff checks
passed; prior protected files/32 rows unchanged, aggregate imports/runner additive.
No unrelated diagnostics/trivial tests. Hosted CI unobserved.

Raw bookkeeping NOT certified FIDE CanClaim/adjudication; no FIDE key/rights-history,
lawful no-earlier-terminal histories, automatic draw/mate precedence/claim protocol,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ or initial value.
Paper and separate adversarial audit saved BEFORE Lean; same-agent review, not
independent external audit. Boundaries99/100,2/3,zeroing/no-reply/pseudo-only controls
symbolic, no concrete full-game diagnostics/enumeration/oracle/certificates/novelty.

Reproduce: `python sessions/evidence/S058/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE c75b3760022717e586a789e47c09c03911a43a56`
Validate: `python sessions/evidence/S058/validate.py`.
