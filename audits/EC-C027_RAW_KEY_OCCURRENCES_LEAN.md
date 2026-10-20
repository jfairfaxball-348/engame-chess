# S042 — Lean fidelity review of EC-C027

Same-agent review, not independent external review. Standalone paper/audit saved
BEFORE Lean. Official core Lean4.35.0, no dependency. No failed compilation.

RawOccurrences/Definitions introduces occurrences for arbitrary K:Type u with
EXPLICIT DecidableEq K and fixed key:Position→K. It counts every position in
frozen t.positions by filtering decide(key(p)=a) and taking length. Root/current
endpoints are included by the unchanged stored list; no count-vector or reset
truncation, arbitrary Boolean equality or erased-history surrogate.

Append has one main append_occurrences for every actual s,m,legal proof and
queried a. It unfolds the definition, rewrites the exact frozen append_spec
position retention equation, then splits on new endpoint key equality. Standard
filter-append and list-length simplification finish both branches. Same map
and queried key on both sides; querying NEW current key in OLD history is
preserved, never replaced by old-current count. Every legal/reset/draw-ending
append is covered without material/turn/strategy/outcome guards.

Incremental lake build passed FIRST attempt, 71 jobs; complete AxiomCheck exit 0.
Exact definition/main printed; main uses [propext, Classical.choice, Quot.sound].
No extra public elementary root/bound/monotonicity theorem; root computation
and nonconsecutive/constant-key/new-current counterexample are symbolic paper
controls, not executed compatible full chess games.

Generic bookkeeping only, no actual FIDE repetition key/effective-ep or rights
history theorem, repetition threshold certificate, claim/adjudication/lifting
or numerical KRK result. Gate F pending until published exact-source fresh run.

## Completed Gate F

Own published exact source `04bd8d03bf09056eff74c5fae1c399a841b170cb`, ONE NEW GitHub clone, no .lake
before build. Full 71-job lake build exit 0, 446.759s; COMPLETE AxiomCheck
exit 0 at 2026-10-20T08:26:11Z. 274 allowed reports, main standard-three only.
Exact definition/main inspected. Working/clean reports identical, all formal
source bytes match own exact source, full source/transitive hashes and clean
HEAD/tree/status retained. Two new modules forbidden scan zero. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim.
No authoring/prebuild/build failure; original and clean checks each passed.
Gate F complete, Gate Z pending; hosted CI unobserved. Evidence: sessions/evidence/S042/.
