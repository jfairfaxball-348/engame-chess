# S043 — EC-C027 Gate Z evidence

Own published SHA `04bd8d03bf09056eff74c5fae1c399a841b170cb`, ONE NEW GitHub clone, no formal/.lake
before build. Full **71-job lake build exit 0, 435.817s**; COMPLETE
**AxiomCheck exit 0**, **274 allowed reports**, UTC **2026-10-20T08:34:45Z**.
Definition/main inspected, main standard-three only. Entire report identical
to actual S042 Gate F. All source/transitive bytes match own anchor/current main.
Full clone/checkout/prebuild/build/axiom/toolchain/lake logs, commands/exits/
timings, source/import hashes, clean HEAD/tree/status, runtime identity and UTC
summary retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependencies/shim, TLS/checksums unchanged. Hosted CI unobserved.

EC-C027 frozen as EC-T0025, both complete RawOccurrences modules, one manifest/
ledger row. All prior formal source/papers/audits/evidence/manifests and 24 rows
preserved; validation/ledger/preservation logs separate. No unrelated diagnostic
suite or trivial tests, no failed/repeated clean run or full compatible game.
Generic key counting only, no FIDE key/repetition certificate or class gain.

```sh
python theorems/frozen/VERIFICATION-S043/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE 04bd8d03bf09056eff74c5fae1c399a841b170cb
python theorems/frozen/VERIFICATION-S043/reproduction/validate.py REPO_ROOT
```
