# S035 exact-source Gate F — EC-C023 raw trace append

Published proof-source `526a298b80ef04541e518a3dcc62f861c8f51c5c`; verified UTC `2026-10-19T14:09:53Z`.

- ONE new GitHub clone `/tmp/engame-s035-gate-f`, detached at the full SHA;
  no formal/.lake BEFORE build. `pre-build.log` records the assertion.
  Full `lake build`: **59 jobs, exit 0, 360.247s** (Bash built-in time).
  This run certifies the new raw-trace obligation, not older historical results.
- Full AxiomCheck: exit 0. Exact Type constructors, state fields, function/step
  signatures and all FOUR main declarations are retained. **265 reports**:
  234 [propext, Classical.choice, Quot.sound], 18 [propext, Quot.sound],
  8 [propext], 5 axiom-free. Each new declaration uses the standard three only.
  No sorryAx/native reduction. Complete working/clean reports byte-identical;
  every Lean source byte matches the exact checkout.
- Five complete source-module hashes: `source-sha256.txt`. Zero forbidden tokens.
  All **336** protected prior formal/theorem/proof/audit/script/test/evidence
  files byte-identical to base main, including EC-T0020 and all earlier frozen
  sources/records. Only aggregate imports and AxiomCheck are additive among
  older Lean files. No frozen source, ledger row or manifest changed.
- Ledger structural check: **20 frozen bundles**, unchanged. No Python
  implementation or ledger change: unrelated historical diagnostic suites
  were not rerun. No new executable example or class-wide test supplies a
  general proof; all four new results are symbolic Lean proofs.
- Official unmodified core Lean 4.35.0 release
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, no dependencies or host shim.
  TLS/checksum verification unchanged. `toolchain.log` records identity.
  Activation: ELAN_HOME=/workspace/.tools/elan and its bin directory on PATH.
- Logs are final successful runs. Hosted CI **unobserved**, not inferred from
  local verification or publication. Reviews are same-agent, not independent
  external reviews. No oracle/tablebase/engine or enumeration supplied a proof.

EC-C023 is FORMAL_VERIFIED, not frozen. Trace is an indexed TYPE of stored
initial-rooted moves, not a Prop-only reachability witness. Append preserves
ordered moves/positions and exact endpoint; raw steps are sound and cover
EVERY kernel-legal reply. Endpoint Arisen is raw-kernel reachability only.
No clock/repetition/admissibility or no-earlier-terminal classifier, full Layer
instance, numerical KRK bound, DTM/DTZ/WDL or Syzygy parity claim. Gate Z stays
pending; S036 targets only the next raw-clock fold component in new modules.
