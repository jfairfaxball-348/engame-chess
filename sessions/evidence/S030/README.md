# S030 exact-source Gate F evidence

Published proof-source: `4acc3e8638a916f329788d4c2b5f0db6f2c9bf67`. Verified UTC: `2026-10-19T12:16:49Z`.

- A new GitHub clone `/tmp/engame-s030-gate-f` was detached at the full SHA;
  absence of `formal/.lake` was asserted before build. `clean-build.log`: exit 0,
  **51 jobs, 336.763 seconds**, timed with Bash built-in time.
- `clean-axioms.log`: `lake env lean AxiomCheck.lean`, exit 0. **259 reports**:
  228 [propext, Classical.choice, Quot.sound]; 18 [propext, Quot.sound];
  8 [propext]; 5 axiom-free. All **24 new public declarations** have full
  axiom and exact statement outputs. No sorryAx or Lean.ofReduceBool.
  Byte-identical to `working-axioms.log`; all Lean source bytes match the clone.
- `source-sha256.txt`: ten new modules. `forbidden-tokens.log`: zero forbidden
  tokens. `preservation.log`: all 100 prior Lean modules/theorem records checked
  byte-identical; S028/S029 and frozen sources unchanged. Only aggregate Lean
  imports and the axiom runner are extended among prior Lean files.
- `python-tests.log`: all **39** existing Python tests passed in **104.760s**;
  none failed or skipped. `ledger-validation.log`: 11 bundles, structure only.
  Fixed new Lean controls cover back-rank preparation, black file-axis setup
  with all rights and an ep flag, and the old naive-setup/capture obstruction.
  These controls and existing Python diagnostics are supplementary; no general
  theorem is supplied by position enumeration, engine or tablebase data.
- `summary.json`, `validation.log` and `verified-utc.txt` retain the exact result.
  Logs report final successful runs, not interim failed elaborations. Hosted CI
  has **not** been observed and is not claimed to have passed.

Official unmodified Lean 4.35.0 release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, core only, no dependencies or host shim.
TLS/checksum verification stayed enabled. Activation:
`export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`.

EC-C019–021 and the completed clock-free EC-C011 are FORMAL_VERIFIED, not frozen.
The full strong theorem requires only exact KRK, strong turn and an incoming
Legal move. Weak forcing is actual mate or nonempty all-noncapturing replies.
There is no remaining setup, axis or weak-classification hypothesis gap in
these statements. Gate Z, clock/repetition and numeric distance semantics remain.
The frozen count stays eleven; no full FIDE WDL/DTZ or seven-piece claim.
Audits are same-agent, not external independent review.
