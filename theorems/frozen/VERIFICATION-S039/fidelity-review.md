# S039 paper-to-Lean fidelity review

Same-agent review, not an independent external audit. Reviewed the EC-C025
paper, both original audits, actual Gate F statement/axiom logs, source hashes
and clean-source identity, and EC-T0021/0022 definitions and frozen boundaries.
No Lean source changes are required. Extends relates full raw states: zero is
exact identity, successor is an actual frozen RawBoardStep. Its witnesses retain
the actual Move, source legality and full prior trace. clock_le_extension uses
induction, frozen append_clock_le, monotonicity and transitivity. No endpoint
clock premise or erased-board history substitution occurs. Reset edges and all
legal replies remain covered; no terminal/material/colour filter was added.

Symbolic controls: zero cannot change state; quiet edge attains parent+1;
reset edge is zero and below parent+1; mixed paths retain the bound and full
history. Equal erasures cannot substitute unrelated trace data. Earlier raw
draws do not invalidate a raw bound when a legal append exists. No particular
initial-rooted promotion/ep/castling or threshold prefix was constructed/run.
The new bundle is the COMPLETE ExtensionDefinitions and ExtensionBound modules,
with one main declaration and unchanged transitive definitions. Standard three
axioms only at Gate F; a NEW exact-source Gate Z run is still required.

No sufficient-budget lifting, numerical KRK mate bound, repetition certificate,
claim/adjudication/FIDE admissibility, full Layer instance, WDL/DTZ/Syzygy or
initial-position result. h+n<100 remains a future certificate hypothesis.
Classical induction, no novelty claim, tablebase, engine or enumeration.
