# Protocol — propose, prove, formalise, freeze

## Gate P: proposed
Record a theorem candidate with unique ID, exact board/rules assumptions, quantifier order, precise result type and known counterexample risks. Status `PROPOSED`. No theorem-ledger row is required for a candidate: use `research/CANDIDATES.md`.

## Gate L: locally verified mathematics
Before touching Lean, write a standalone proof in `research/` or `proofs/` with:
- Unambiguous definitions for every symbol; distinguish reachability from play stopped by rules.
- Proof of required lemmas, including preservation of legality under every relevant move.
- Adversarial counterexample search: illegal placements, boundaries, side-to-move, path length zero, opponent cooperation, definitions of check/checkmate, and all declared rules.
- An independent audit note listing attempted falsifications and outcomes.
- Source attribution. Classical results must not be described as novel.

Once every gap is resolved, mark the candidate `LOCAL_VERIFIED`; keep evidence and reviewer/session reference. **Computational evidence alone is insufficient.**

## Gate F: formal verification
Implement the exact local statement in Lean 4, preferably using mathlib if it decreases trusted code. Pin the `lean-toolchain` and `lakefile` dependency revisions as soon as a Lean project is introduced. The formal theorem must correspond to the prose statement: do not replace chess legality with a weaker surrogate without stating that reduction and proving it.

Required checks at the referenced commit:
- `lake build` successful in a clean reproducible checkout.
- No `sorry`, `admit`, unjustified `axiom`, `unsafe` proof escapes or fabricated proof tokens.
- `#print axioms <qualified_theorem_name>` inspected and recorded.
- Audit all imported axioms and the trusted kernel assumptions.
- Verify no incorrect coercion of a finite test or a tautology into the intended theorem.
- Save full build logs/toolchain revision and proof declaration name.

Set `FORMAL_VERIFIED` only once evidence exists.

### Re-checking obligations (incremental verification)
The library will hold many small proofs. They are **not** all re-verified on every commit.
- **One module per theorem** (`formal/EndgameChess/<Topic>.lean`). Definitions shared by several theorems live in their own modules and are imported.
- **Lean CI** (`.github/workflows/lean-build.yml`) runs only when `formal/**` changes. It restores the cached `formal/.lake`, so `lake build` rebuilds only the changed modules and the modules that import them.
- **What must be re-checked:**
  1. a new or edited proof module;
  2. every module downstream of a changed shared definition, frozen ones included, because the statement's meaning may have changed;
  3. everything, after a toolchain or dependency bump (the cache key changes).
  Nothing else is an obligation.
- **The full clean-checkout verification above** is a one-off at Gate F and again at Gate Z, for the theorem being certified only. It is not a per-commit duty for the rest of the library.

## Gate Z: freeze
Create an immutable theorem statement/proof manifest under `theorems/frozen/<ID>/` which records: ID, theorem statement and scope, rule edition, local proof audit, Lean source path/declaration, toolchain/dependency revisions, full verified **proof-source commit SHA**, axiom-check findings, clean build evidence, date and version. Then add a single `FROZEN` row to `theorems/LEDGER.csv`. Reference the already-created verified proof-source commit, avoiding a circular reference to the commit containing its own ledger row.

A frozen theorem's Lean module is **never edited**. A correction is a new module or declaration plus a superseding manifest version. Shared modules a frozen theorem imports may change only if CI shows the frozen module still builds, with the same statement and the same axioms. Frozen proofs are not quietly edited or reclassified. If a defect is discovered, append a conspicuous correction/superseding record and update ledger history via an additional auditable commit. Git history is the permanent record; an optional immutable Git tag can additionally anchor each release.

## Permitted status transitions
`PROPOSED → LOCAL_VERIFIED → FORMAL_VERIFIED → FROZEN`. A falsified candidate becomes `REJECTED` *in the candidate register only*, with a concrete counterexample. A blocked claim remains in its current stage. No 'all clear' or theorem count until the actual checks have run.

## Session closeout
Each session must record: changes and links; proven, conjectured, computationally tested and blocked findings separately; checks actually run (or 'not run'); exact commit/tree state; ledger effect; and full text of the installed next session prompt. Never imply that a remote CI job passed just because a workflow file was committed.
