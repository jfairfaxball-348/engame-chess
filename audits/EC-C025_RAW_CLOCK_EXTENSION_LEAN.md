# S038 — Lean fidelity review of EC-C025

Same-agent review, not independent external review. Standalone paper and
adversarial audit saved before Lean. Official core Lean 4.35.0, no dependency.

ExtensionDefinitions adds Extends on full RawTrace.State endpoints. refl is
exact state reflexivity at zero; snoc adds a frozen RawBoardStep with its actual
Move, legality witness and exact append equality. No clock premise, erased-board
replacement, arbitrary seed, terminal guard, material or colour filter occurs.
ExtensionBound has one main theorem clock_le_extension, exactly the paper's
universal bound. Induction on Extends uses append_clock_le at the actual last
edge, transitivity and monotone addition, normalized by associativity. Resets
are covered by that frozen one-step theorem. No length hypothesis is introduced.
No redundant prefix or exact-length theorem is added; represented subderivations
can use the same bound. Full append retention follows from the frozen definition
and append_spec; no frozen source changes.

Incremental lake build passed (68 jobs), followed by complete AxiomCheck exit 0.
The exact new statement and Extends constructors print in the report; new main
uses [propext, Classical.choice, Quot.sound]. Initial compile failed because a
line break after `using` parsed the applied term incorrectly; parentheses fixed
syntax without changing the statement or argument. Full failure log retained.
Gate F remains pending until the published exact commit passes a fresh clone.
No symbolic control is represented as a run of a full example game. No sufficient
budget lifting, numerical KRK bound, repetition or full FIDE result is claimed.

## Completed Gate F

Published proof-source `22243b9ca5769e1478c75a333befa3c8465c90f2` before ONE NEW GitHub clone,
detached at that exact SHA, formal/.lake absent before full build. Full lake
build: 68 jobs, exit 0, 472.858s; COMPLETE AxiomCheck exit 0 at 2026-10-20T07:44:55Z.
272 allowed reports, including 5 axiom-free; new main standard-three only.
Exact statement/constructors printed; full working/clean runner outputs
byte-identical. All Lean source/import bytes match; complete source/transitive
hashes and clean-source identities retained. Two new modules forbidden scan
zero. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
executable hash matches preceding freeze evidence. No dependencies or shim.
Gate F passed, Gate Z pending. Hosted CI unobserved. Evidence: sessions/evidence/S038/.
