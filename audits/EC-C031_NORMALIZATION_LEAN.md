# EC-C031 — Lean fidelity review

S050. Same-agent review, not independent external audit. NEW shared definition
normalizeEP exactly replaces ep by frozen effectiveEP. One main theorem module
imports frozen OrdinaryEP/EPCharacterization without edits. Complete q,m statement
matches paper: Boolean legal equality plus full played Position equality for
actual original legal moves. Available branch normalizeEP=q. Absent branch
splits precise raw shape; actual legality would yield forbidden LegalEP witness;
normalized isPseudo false by source pawn, nonzero dx, empty dst and none marker.
Ordinary branch invokes frozen marker lemma then rewrites exact play/isPseudo
before applying actual self-check test with same turn. No raw illegal EP endpoint
equality assumed, no adverse reply pruning, enumeration or extra game premise.

Initial incremental proof failed only because simp unfolded normalizeEP before
using ordinary-branch equalities. Explicit change/rw resolved this unchanged
statement; full failure log retained. Final 77-job incremental build and COMPLETE
working AxiomCheck passed without warnings, 278 allowed reports, main standard
three. Gate F pending. No unrelated diagnostics or concrete full-game run.

## Observed Gate F

Own proof-source `4d47b33549fc5286099cae0bd89de76b05fbeb42`; NEW GitHub clone `/tmp/engame-s050-gate-f`, no .lake before build. Full 77-job build exit 0 in 469.893s, COMPLETE AxiomCheck exit 0 at 2026-10-20T12:23:48Z; 278 allowed reports, main standard-three. Full working/clean report byte-identical.
Full source/transitive hashes, clean HEAD/tree/status and command/exits/times
retained; exact main inspected, forbidden scan zero. Official core Lean4.35.0,
no dependency/shim. No clean-build failure/repetition. Hosted CI unobserved.
