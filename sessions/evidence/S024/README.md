# S024 Gate F evidence

- Proof-source: `fca2ca88c8391b1d2bd49c3db9f2fa04258a4a87`, published on `session/s024-krk-forcing` before fresh verification.
- Gate F completed UTC: `2026-10-19T06:56:09Z`.
- `clean-build.log`: fresh GitHub clone, absent `.lake`, core-only Lean 4.35.0, 26 jobs, 236.09 seconds, exit 0.
- `clean-axioms.log`: full exact-source axiom and statement report, 180 declarations; 19 added in S024. All subsets of propext/Classical.choice/Quot.sound. No sorryAx or ofReduceBool.
- `source-sha256.txt`: hashes of the four new modules; checked against the closeout tree. No existing proof module was edited.
- `forbidden-tokens.log`: zero forbidden tokens in the new modules.
- `negative-controls.log`: three false fixed-configuration claims rejected by Lean.
- `python-tests.log`: all 33 tests passed. No extra Python implementation tests were added for the Lean proofs.

The host uses the retained executable-path shim described in `theorems/frozen/EC-T0007/verification-environment.md`. It substitutes `/proc/self/exe` only for the denied own-process executable-path query; it does not change a proof, axiom or kernel routine.

These are Gate F logs, not Gate Z evidence. EC-C009 and EC-C010 remain unfrozen until S025. Full clock-free KRK forcing (EC-C011) is still PROPOSED. No remote CI result is asserted.
