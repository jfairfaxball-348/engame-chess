# S028 exact-source Gate F evidence

- Proof-source: `cb5d3bb713257d7cac8e3c1f9d82d8e77b746d6c`, pushed before verification on `session/s028-reentry`.
- Fresh GitHub clone `/tmp/engame-s028-gate-f`, detached at that exact commit. `formal/.lake` absence asserted before build. New `clean-build.log`: `lake build`, exit 0, 34 jobs, 265.586 seconds (Bash built-in timing).
- `clean-axioms.log`: `lake env lean AxiomCheck.lean`, exit 0. All 212 axiom reports allowed: 189 [propext, Classical.choice, Quot.sound]; 10 [propext, Quot.sound]; 8 [propext]; 5 axiom-free. Fifteen new declarations, including all fixed controls, with exact `#check` outputs in the same report. Full clean and working reports are byte-identical. No sorryAx or Lean.ofReduceBool.
- Gate F completed UTC: `2026-10-19T09:06:21Z`. `summary.json` and `validation.log` record the count and identity checks.
- `source-sha256.txt`: five new Lean modules. All working Lean sources match the fresh proof-source checkout, including aggregate imports and AxiomCheck. No frozen module changed.
- `forbidden-tokens.log`: zero word-bounded forbidden tokens in all five new modules. `preservation.log`: all earlier theorem records and proof modules unchanged; frozen ledger remains 11.
- `python-tests.log`: 36 tests, exit 0, 101.765 seconds. `ledger-validation.log`: 11 frozen bundles, structural only.
- `control-prefixes.log`: separately checked legal four-ply arrivals for the corner, lower-band crossing and upper-band rescue inputs; the chase prefix is already part of the compiled Lean witness.
- `reentry-diagnostic.json`: 24 chosen phase inputs, 194 image returns; 12 chosen three-margin rank raises, 44 replies; 2 two-margin rescue inputs in both colours, 10 first replies, 2 hanging branches and 10 repair replies. Four failed-policy controls. Local ray-walking error finding only, no class graph or value calculation in this new diagnostic. The existing Python suite's exhaustive diagnostics are also supplementary, not proof.

Core-only official Lean 4.35.0, release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No LD_PRELOAD shim, modified compiler/kernel routine, external dependency, tablebase or engine oracle. Activate with `ELAN_HOME=/workspace/.tools/elan` and prepend `$ELAN_HOME/bin` to PATH. Lake commands run in `formal/`, Python commands at repository root.

The working build encountered and corrected ordinary projection/extensionality elaboration issues before this proof-source was committed; only final successful source is anchored here. A transient tool transport disconnect during polling did not replace or restart the original clean build; its final result was observed. Hosted CI is not claimed as observed.

EC-C014 and EC-C015 are FORMAL_VERIFIED, not frozen. EC-C011 remains PROPOSED: non-aligned lower-band pursuit/tempo and a recursively usable post-contraction invariant remain unproved; arbitrary-arrival setup is separate. No full KRK WDL, clock/repetition or initial-position claim follows. Same-agent audits, not independent external review.
