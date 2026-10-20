# S070 — exact-source Gate F for EC-C041

Own published proof-source `fe7efa687ae1481db405cf8808d9ad3437906861`. ONE NEW GitHub clone `/workspace/engame-chess/work/s070-gate-f`,
formal/.lake absent before full build. 130-job build exit 0 in
397.623s; COMPLETE AxiomCheck exit 0 at 2026-10-20T18:18:15Z, 320
permitted reports. All 9 new declarations and exact statements inspected.
Full working/clean runner byte-identical; all formal source bytes identical.

11 complete new KRKStrategy modules, source/import/executable SHA256, clean
HEAD/tree/status, official core Lean4.35.0 and full command logs/exits/times/UTC
retained. No fresh build failure/retry. No dependency/shim/TLS/checksum changes;
hosted CI unobserved. Working authoring failures and exact repairs retained,
with actual timings. Separate same-agent paper/Lean audits, not external review.
Reproduce verify.py in NEW output/clone, using the own proof source above.

Exact result: both colours/arbitrary flags, every legal strong-turn KRK arrival
has a minimal-budget policy, rank≤508, full-line pairwise distinct normalized raw
keys, ≤509 vertices, all legal weak replies and terminal iff named mate at a
winning policy node. Equal-key budget invariance and natural well-ordering are
proved; no solver/table/per-position certificate. The policy differs from the
frozen geometric policy and from arbitrary raw play.

Incoming stored-history counts, clock budget, RAW-to-FIDE correctness and complete
KRK outcomes/distances remain open. 508 exceeds 100. Gate Z separate; 37 frozen
bundles unchanged. Relevant ledger/preservation/document/full-table/full-prompt/
links/diff checks passed; no unrelated diagnostics or tests.
