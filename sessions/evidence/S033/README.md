# S033 exact-source Gate F — EC-C022

Published proof-source: `55affd0a7a3f2e77335f4964ae4fbc1edbe19e05`. Verified UTC: `2026-10-19T13:35:50Z`.

- ONE new GitHub clone `/tmp/engame-s033-gate-f`, detached at the full published
  SHA; no `formal/.lake` before `lake build`. `pre-build.log` records that
  precondition. `clean-build.log`: **54 jobs, exit 0, 369.671s**, timed with
  Bash built-in time. Only this new Gate F obligation was certified.
- `lake env lean AxiomCheck.lean`: exit 0; full report in `clean-axioms.log`.
  Includes the exact Layer fields and definition signatures plus BOTH new
  exact theorem statements and axiom reports. **261** total reports:
  230 [propext, Classical.choice, Quot.sound], 18 [propext, Quot.sound],
  8 [propext], 5 axiom-free. Both new main theorems use the standard three only.
  No sorryAx or native reduction. Working and clean reports byte-identical;
  every Lean source byte matches the exact clone.
- `source-sha256.txt`: all three complete new modules. Zero word-bounded
  forbidden tokens. `preservation.log`: all **294** protected prior files
  unchanged, including frozen modules, manifests, ledger, papers/audits,
  scripts/tests and prior evidence. Only additive aggregate imports/runner
  entries change among older Lean files.
- `ledger-validation.log`: **19 frozen bundles**, structural check only.
  No Python implementation or ledger change; historical diagnostic suites
  were not rerun. The general proofs, not fixed tests or enumeration, certify
  this abstract theorem. No new example is claimed as compiled evidence.
- `toolchain.log`: official core Lean 4.35.0, release
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; no dependencies, host shim or
  change to TLS/checksum verification. Activation uses `/workspace/.tools/elan`.
- Logs are final successful runs. An initial local missing-target command used
  a nested path prefix; files were moved to the correct paths before the
  successful incremental build. That failure is not counted as success.
  Hosted CI remains **unobserved**; no inferred CI claim.

EC-C022 is FORMAL_VERIFIED, not frozen. Both results apply to any abstract
Layer with ongoing move soundness, coverage of EVERY raw legal reply and
ongoing nondeadness. Same n in both finite-budget predicates. No concrete FIDE
history instantiation, converse, holding/determinacy, numerical KRK distance,
full WDL/DTZ, Syzygy parity or initial-position result. Gate Z is separate.
Reviews are same-agent, not independent external reviews.
