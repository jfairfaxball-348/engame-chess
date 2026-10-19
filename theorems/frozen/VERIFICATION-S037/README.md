# S037 — Separate raw trace / counter Gate Z records

EC-C023 → [EC-T0021](../EC-T0021/v1.md), source `526a298b80ef04541e518a3dcc62f861c8f51c5c`.
EC-C024 → [EC-T0022](../EC-T0022/v1.md), source `2d2b40ddaaff2a962bb9f573e8de799b1427d5f8`.
Two NEW sequential GitHub clones, own exact published anchors, formal/.lake
absent before each build. Full builds **59/66 jobs, exits 0**, followed by
complete AxiomCheck **exits 0**, **265/271 allowed reports**. All ten public
statements checked; full runner outputs byte-identical to actual Gate F logs.

Each candidate directory retains clone/checkout/pre-build logs, full lake build,
full axiom/statement output, toolchain/lake identity, command exits/timings,
source and transitive dependency SHA-256 inventories and UTC summary.
RawClock closure includes all five RawTrace imports, unchanged at BOTH anchors.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependencies/host shim, unchanged TLS/checksum verification. Git proxy and
existing elan setup reused. Hosted CI unobserved.

Reproduce ONCE per obligation with NEW output/clone paths:

```sh
python theorems/frozen/VERIFICATION-S037/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE EC-C023
# After the first completes:
python theorems/frozen/VERIFICATION-S037/reproduction/verify.py REPO_ROOT NEW_OUTPUT_2 NEW_CLONE_2 EC-C024
python theorems/frozen/VERIFICATION-S037/reproduction/validate.py REPO_ROOT
```

EC-C023/postprocess-interruption.log retains an evidence-comparison interruption
after BOTH Lean commands had passed; finalize.py completed corrected inspection
without rerunning either Lean command. Current main's aggregate runner/import
files add S036 counter entries to the earlier trace source; historical aggregate
hashes are retained at their own anchor and additions checked separately.
Validation/preservation/ledger-test logs are separate. Prior 20 ledger rows,
all formal sources, previous manifests/papers/audits/evidence preserved.
22 bundles are not 22 solved classes. Raw traces/counter do not establish full
FIDE history/adjudication, a sufficient clock/repetition budget, numeric KRK
distance, DTM/DTZ/WDL/Syzygy parity or initial-position value.
