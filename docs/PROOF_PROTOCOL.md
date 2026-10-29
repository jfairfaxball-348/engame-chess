# Minimal proof and freeze standard

This document governs **mathematical trust**, not work sessions. An interactive session may contain several proofs, freezes or none. No separate proof/freeze session, numbered handover, full progress table, mandatory status report, or repeated session evidence bundle is needed.

## 1. Research the active obligation
Start with the open mathematical obligation in [current work](../NEXT_SESSION.md). Use existing results first. A necessary auxiliary lemma, diagnostic or counterexample search is legitimate; it must feed the actual obligation rather than create a parallel theorem-count programme. Failed attempts need recording only when their counterexample or insight materially affects the next proof. Paper notes belong with the relevant proof, not in a session diary.

## 2. Prove the statement (LOCAL_VERIFIED)
Write the mathematical claim and argument in `proofs/` or `research/` with precise input domain, rule model, move and quantifier semantics, and all essential lemmas. Stress-test legality, captures, terminal branches, repetition, clock thresholds, side to move, and adversarial replies as applicable. Resolve genuine gaps before claiming a proof. Counterexample scripts are diagnostics, not substitutes for general proof. Keep a brief proof critique/caveat inside the proof itself (or a separate audit when substantive). A candidate may remain open without an administrative status-change document.

## 3. Formalise and check (FORMAL_VERIFIED)
Represent the actual claim faithfully in Lean 4, not a weaker surrogate. Give each principal result an identifiable module/declaration and add new exported main declarations to `formal/AxiomCheck.lean`. At verification, record the pinned toolchain/dependencies, exact source commit and declaration, a successful reproducible `lake build`, the `#print axioms` output/allowed assumptions, and any material limitations of the prose–Lean bridge. Disallow `sorry`, `admit`, ad hoc proof axioms or unsafe escapes. Inspect non-vacuity and audit any nonstandard assumptions.

Verification is **incremental** for day-to-day work: changed modules and their dependants, including frozen consumers of changed shared definitions. A clean checkout is required **once for certification**, not again just because a session ended or a separate freeze session was scheduled. A single verified source and captured evidence can support both FORMAL_VERIFIED and its subsequent freeze without a duplicated full build. Do not claim external CI/Palomar checks unless their results were observed.

## 4. Freeze a verified result (FROZEN)
When ready, create one compact `theorems/frozen/<ID>/vN.md` manifest containing:
- Exact proved statement, scope, rules and known boundaries; proof and relevant audit links.
- Lean path/declaration, pinned Lean toolchain/dependencies, **verified proof-source commit SHA**, checks and any accepted axioms/trust assumptions.
- Date/version and relationship to previous frozen claims, when relevant.

Then add **one** `FROZEN` row to `theorems/LEDGER.csv`. Keep the ledger schema and existing rows intact. One verified proof-source commit plus one manifest/ledger commit is enough; no mandatory intervening session, fresh duplicate build, log-copy factory or separate session closeout. Preserve only the essential reproducibility evidence and genuine mathematical caveats.

A frozen theorem module and historical manifest are immutable. Corrections or strengthening require a new module/declaration and a conspicuous new or superseding manifest; never rewrite history. Toolchain migrations are distinct from theorem changes: rebuild and check affected declarations with unchanged statements and justified axioms, recording a concise migration provenance instead of manufacturing per-theorem session reports.

## 5. Progress means mathematical coverage
Advance to the next **obligation**, not the next session number. Only claim a material class closed when its [Syzygy-parity](CHARTER.md#parity-target-hard-boundary-owner-2026-10-29) WDL50 and DTZ50 information for all fresh legal positions, both turns, has actually been covered by checked mathematics. The theorem count is not the number of solved endgames.

Update the short [live work note](../NEXT_SESSION.md) if the key open obligation changes, the [roadmap](ROADMAP.md) if a class milestone changes, and the immutable theorem ledger **only on a genuine freeze**. No other routine reporting is required. Existing `sessions/` and old evidence remain historical records, not a process to repeat.
