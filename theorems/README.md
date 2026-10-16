# Immutable theorem ledger

`LEDGER.csv` records **only completed, FROZEN theorems**, not candidates, proposed proofs, draft Lean projects or tests. The ledger is initially header-only because zero theorems have passed the full protocol.

Each row must identify one precise theorem, its proof statement, locally audited mathematical proof, exact Lean source and declaration, compiler version, the immutable 40-hex-character Git commit SHA containing the **verified Lean proof**, build/axiom verification timestamp, pinned chess rule edition and a freeze manifest.

Recommended on-disk manifest: `theorems/frozen/EC-T0001/v1.md`. Place supporting logs under that directory or link to an immutable artifact containing them. The manifest is not a substitute for independent code review.

The freeze commit must be **later than** its referenced verified proof commit so it can cite an existing Git SHA; do not attempt a self-referential commit hash. An additional tag may anchor the ledger commit.

Corrections require a new versioned entry and clearly visible supersession note; Git history must preserve the original record. No ledger row or proof file may be rewritten without that provenance. The checker `scripts/validate_ledger.py` checks *format/integrity only*; it is not a mathematical proof checker.

Current frozen count: **1** — [EC-T0001](frozen/EC-T0001/v1.md) (K vs K dead position, frozen S003).
