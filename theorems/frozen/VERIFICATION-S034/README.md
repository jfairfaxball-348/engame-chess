# S034 — new Gate Z verification of EC-C022 / EC-T0020

Proof-source `55affd0a7a3f2e77335f4964ae4fbc1edbe19e05`, verified UTC `2026-10-19T13:52:54Z`. ONE new GitHub clone
`/tmp/engame-s034-gate-z`, no formal/.lake before build. This is separate from
S033 Gate F. Full build **54 jobs, exit 0, 371.256s**. Exact interface,
statements and axiom runner exit 0; both main declarations have only the
standard three axioms. All **261** whole-run reports allowed (230 standard-
three, 18 propext/Quot.sound, 8 propext, 5 axiom-free). TWO public declarations
belong to this bundle. Full report byte-identical to S033 Gate F.

`commands.json` records exact commands, working directories, exit codes and
wall times; clone/checkout/pre-build logs prove the new-checkout precondition.
Toolchain/lake logs identify official core Lean 4.35.0 release
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No dependencies, host shim or
change to TLS/checksum verification. `summary.json` retains counts and scopes.
No failed build is counted as success; no historical certification was repeated.

Complete anchor Lean/config hashes: `source-sha256.txt`. Full transitive
closure: `dependency-sha256.txt`. Both declarations: `declarations.txt`.
Three whole new modules, including shared definitions and all private/generated
implementation details, belong to EC-T0020. Forbidden token matches: zero.
All anchor source bytes match the working tree. Prior source/manifest/audit/
evidence bytes and the prior ledger prefix are checked in `preservation.log`.
Ledger structure/tests and record validation are separate structural checks,
not mathematical proofs; their actual results are retained alongside this file.
Observed: six ledger-validator tests passed; structural validation reports
twenty frozen rows. Preservation checks confirm 366 prior tracked files
unchanged and the original nineteen-row ledger bytes as an exact prefix.
Complete table/prompt reproduction and local manifest links were checked.

`reproduction/verify.py` can reproduce this run using a NEW clone and output
directory; it refuses to overwrite completed evidence. `reproduction/validate.py`
checks the published record/preservation without a rebuild. Hosted CI remains
**unobserved**. Local build success or publication does not imply CI success.

Scope is the generic SAME-BUDGET conditional projection, not FIDE-history
instantiation, a converse, holding/determinacy, numerical KRK bounds, full
WDL/DTZ or Syzygy parity. Reviews are same-agent, not independent external
reviews. No oracle/tablebase/enumeration supplies a proof. Twenty frozen
bundles are not twenty solved material classes; S035 begins a raw-trace component.
