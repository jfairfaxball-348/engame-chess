# S068 — exact-source Gate F evidence

Own published proof-source `3a4a543625673383f66de70a8f847e340d820570`. NEW GitHub clone `/workspace/engame-chess/work/s068-gate-f`,
formal/.lake absent before full build. Build exit0, 119 jobs,
399.429s; complete AxiomCheck exit0, 311 allowed reports at
2026-10-20T17:58:38Z. All 24 new public declarations in declarations.txt
and their exact statements inspected. Every axiom report is within propext,
Classical.choice, Quot.sound (axiom-free declarations permitted). Entire working
and clean runner byte-identical; all formal source bytes identical.

27 complete new Rules/KRKBound modules; source and complete transitive hashes,
clean HEAD/tree/status, official executable checksum/toolchain and full command
logs/exits/times/UTC retained. Official core Lean4.35.0, no dependency/shim/TLS/
checksum changes. One fresh build; no fresh failure/retry. Hosted CI unobserved.
Run verify.py with REPO_ROOT OUTPUT_DIRECTORY NEW_CLONE_DIRECTORY PROOF_SOURCE_SHA
for a new reproduction; do not overwrite completed evidence.

Authoring failures and fixes in authoring-failures.md, logs retained. First
working attempts did not capture timings; that limitation is explicit. Final
working axiom command is in working-commands.jsonl. Changed modules and importer
passed locally before publishing source. Same-agent separate fidelity review
at audits/EC-C040_KRK_QUANTITATIVE_LEAN.md; not independent external review.

Exact result: both colours/arbitrary target flags, exact strong-turn KRK and
no weak check (hence any legal incoming move), MateWithin at 508; wall 84*(7−R.y),
pursuit8*m+E and same-budget noRights transport. No full FIDE history, exact
distance, numerical optimality or class-coverage claim. 508 exceeds100.

Preservation and relevant ledger tests passed. Existing formal modules/frozen
records/ledger unchanged; only aggregate imports and AxiomCheck extended.
Gate Z remains separate. Mathematical progress beyond this bound is not inferred.
