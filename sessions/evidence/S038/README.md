# S038 — EC-C025 exact-source Gate F evidence

Published source `22243b9ca5769e1478c75a333befa3c8465c90f2`, ONE NEW GitHub clone
`/tmp/engame-s038-gate-f`, detached at exact SHA. formal/.lake absent before build.
Full lake build **68 jobs, exit 0, 472.858s**; complete AxiomCheck **exit 0**,
verified UTC **2026-10-20T07:44:55Z**. **272** allowed reports; new main
EndgameChess.Rules.RawClock.clock_le_extension uses standard three only.
Official core Lean 4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies; executable hash matches preceding S037 official identity.

- commands.json: actual commands, exits and elapsed times.
- clone.log, checkout.log, pre-build.log: fresh exact-source identity before build.
- toolchain.log, lake-version.log, runtime-identity.json: official runtime identity.
- lake-build.log, axioms-statements.log: full fresh build and complete statements/axioms.
- working-build.log, working-axioms.log: successful incremental authoring checks.
- initial-build-failure.log: retained syntax failure before correction.
- source-sha256.txt, dependency-sha256.txt: full source and transitive closure.
- clean-source-identity.json: exact commit/tree and clean tracked/untracked state.
- summary.json: completed result and declaration-specific axioms.
- forbidden-tokens.log, preservation.log, ledger-validation.log, validation.log:
  source/record/evidence/document checks, separate from Lean verification.

Complete runner output byte-identical to working report; every Lean source
matches exact fresh source. All prior source/papers/audits/evidence/ledger bytes
preserved; aggregate imports/runner only add entries. No new frozen row/manifest.
No unrelated diagnostic suite or trivial tests. Controls are symbolic, with no
fixed promotion/ep/castling full game prefix run. Hosted CI **unobserved**.

Reproduce only for a new obligation using NEW output/clone paths:

```sh
python sessions/evidence/S038/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE 22243b9ca5769e1478c75a333befa3c8465c90f2
python sessions/evidence/S038/validate.py
```

The verifier's post-launch comparison path was generalized for NEW output
locations; see reproducer-note.md. No Lean source or actual commands changed.
This is raw counter growth, not sufficient-budget lifting, a numerical KRK
mate bound, repetition/FIDE adjudication or a new solved material class.
