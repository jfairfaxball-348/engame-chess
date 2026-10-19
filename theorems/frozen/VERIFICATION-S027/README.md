# S027 fresh exact-source Gate Z verification

Proof-source: `e8daef6daee088c3adaf1c21b51c0a8f1e31103d`. Verified UTC: `2026-10-19T08:42:13Z`.

A new `git clone --no-checkout https://github.com/jfairfaxball-348/engame-chess.git /tmp/engame-s027-gate-z` was detached at that SHA. Absence of `formal/.lake` was asserted before `lake build`. Logs here were created by this S027 run; S026/onboarding logs were not reused.

- `lake_build.log`: clean build, 29 jobs, 202.297 seconds, success. The unavailable `/usr/bin/time` command initially prevented launch; the actual retained run used Bash's built-in `time` and preserved the Lake exit status. A brief tool transport disconnect occurred during polling; the original build completed successfully and its log was retained.
- `axioms.log`: `lake env lean AxiomCheck.lean`, exit 0, 197 declarations: 174 standard-three, 10 propext/Quot.sound, 8 propext-only, 5 axiom-free. All sets inspected against the allowlist; no `sorryAx` or `Lean.ofReduceBool`.
- `statements.log`: `lake env lean /tmp/s027-statements.lean`, exit 0; the exact input is `statement-commands.txt`. All 17 S026 theorem declarations checked and their axiom sets inspected. Definitions and proof statements inspected against the two paper proofs and same-agent audits.
- `source-sha256.txt`: all Lean sources in the exact-source checkout before building. Every working Lean source matches; no Lean edits in S027.
- `forbidden_tokens.log`: word-bounded scan of Safety, CheckProgress and Examples, zero matches.
- `python-tests.log`: new root `python3 -m unittest discover -s tests -v`, exit 0; 33 tests, 102.003 seconds. Diagnostic computations are supplementary, not proofs.
- `ledger-validation.log`: 11 frozen bundles, structural validation only. `preservation.log` confirms earlier nine rows/manifests and all Lean sources unchanged.

Official core Lean 4.35.0 release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Activation: `export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`. **No executable-path shim or LD_PRELOAD workaround was used on this host.** No compiler/kernel routine or expected artifact checksum was replaced. The older host workaround documented with EC-T0007 is not a requirement of these new runs.

EC-C012 → EC-T0010, EC-C013 → EC-T0011. General KRK forcing remains PROPOSED. Both colours and arbitrary flags are covered; the phase needs four-file separation, same-file kings two ranks apart, strong turn and rook off the lone king's rank. No general WDL, clock/repetition or initial-position claim. No external audit or hosted CI pass is claimed.
