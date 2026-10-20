# S040 — EC-C026 Gate F evidence

Own published source `dd24ef3b4bd68d429c9c381908a7f3d5bfa9f85f`, ONE NEW GitHub clone
`/tmp/engame-s040-gate-f`, no formal/.lake before build. Full **69-job build,
exit 0, 442.648s**; COMPLETE AxiomCheck **exit 0**, **273 allowed reports**,
UTC **2026-10-20T08:07:13Z**. Main standard-three only. Full clean/working reports identical;
all source/transitive hashes and clean-source identity retained. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim.

commands.json retains clone, initial short-SHA checkout, exact FULL-SHA checkout,
toolchain/lake queries and ONE build/runner with exits/timings. Initial strict
HEAD assertion failed BEFORE any Lean command; initial-prebuild-failure.log
and initial-checkout.log record it. Same fresh clone resumed with exact SHA and
no .lake; no Lean command was repeated. Retained verifier has a guarded
--resume-prebuild option; default reproduction still requires a NEW clone.

Full lake-build.log, axioms-statements.log, working-build/axioms, source and
transitive hashes, toolchain/runtime identity, clean HEAD/tree/status, summary,
forbidden-token, preservation, ledger and document validation logs retained.
No unrelated diagnostics or new trivial tests. All prior source/records and
23 frozen ledger rows unchanged; aggregate imports/runner additive only.
No full compatible promotion/ep/castling/threshold game run. Hosted CI unobserved.

```sh
python sessions/evidence/S040/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE dd24ef3b4bd68d429c9c381908a7f3d5bfa9f85f
python sessions/evidence/S040/validate.py
```

Conditional clock certificate only, not repetition/FIDE CanClaim semantics,
sufficient-budget lifting, numerical KRK mate bounds or new solved classes.
