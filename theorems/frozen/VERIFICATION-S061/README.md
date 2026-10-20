# S061 — Raw endpoint classifier Gate Z

Own source `c3cbef551dbf7e16d002815d0a508540439e6ef6`; NEW GitHub clone `/tmp/engame-s061-gate-z`, no .lake before build. Full 86-job build exit 0, 492.419s; COMPLETE AxiomCheck exit 0 at 2026-10-20T14:02:36Z, 283 allowed reports. Main standard-three; full report identical to S060 Gate F.

Raw mate-first classify returns opposite-turn winner at MatedK, draw at remaining
stalemate/dead/150-ply/fivefold triggers, otherwise ongoing. EXACT ongoing iff
nondead, some actual Legal successor, clock<150/count<5. No-successor check Bool
split gives mate/stale forward; converse successor refutes both, remaining draw
triggers false. Optional100/3 claims separate. All raw states/traces/flags/colours,
no legal reply pruning/history/material filter. Raw malformed mate/fivefold overlap
priority is definition, NOT extra FIDE9.6.1 priority; lawful-history proof outstanding.

Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change. One new clean run, no failure/repeated build.
No source edit/incremental build. Relevant ledger tests/structure, preservation/
evidence/full-table/full-prompt/local-link/diff checks passed; prior protected files
and33 rows unchanged, exactly EC-T0034 appended. No unrelated diagnostics/trivial
tests; hosted CI unobserved.

Raw component NOT certified full FIDE adjudication. No key/rights-history identity,
no-earlier-terminal histories/real claim protocol, full FIDE Layer/strategy lifting,
numerical KRK, holding/outcome, WDL/DTZ or initial value. Same-agent audit, not
independent external review; symbolic149/150,4/5,optional100/3,overlap/no-successor
controls, no actual full-game diagnostic/enumeration/oracle/certificates/novelty.
Existing S032 rules mapping retained, no new source retrieval.

Reproduce: `python theorems/frozen/VERIFICATION-S061/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE c3cbef551dbf7e16d002815d0a508540439e6ef6`
Validate: `python theorems/frozen/VERIFICATION-S061/reproduction/validate.py REPO_ROOT`.
