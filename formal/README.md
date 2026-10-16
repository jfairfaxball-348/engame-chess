# Lean 4 proof staging

**Intentionally not initialised yet.** This directory is reserved for a pinned Lean 4 project after the first theorem has passed its *local mathematical* audit. Creating Lean proof declarations now would invite a formalisation disconnected from the carefully reviewed statement.

For the first formalisation session:
1. Pin `lean-toolchain` and `lakefile.toml` (including mathlib revision if used).
2. Model `Fin 8 × Fin 8` squares, king adjacency via Chebyshev distance (or an equivalent explicitly proved definition), and core legal KK transitions.
3. Prove nonadjacency/in-check invariants and finite-path closure.
4. Prove the exact no-checkmate/no-possible-mate claim. The FIDE dead-position rule may remain a *clearly identified rule axiom/interpretation* or be defined as an explicit mathematical predicate; do not silently claim Lean has verified FIDE's normative text.
5. Compile in a clean checkout; check `#print axioms`, no `sorry`, and record the exact proof-source commit and Lean toolchain.
6. Only then prepare the frozen manifest/ledger gate.

**No Lean build or verified theorem is claimed by this bootstrap.**
