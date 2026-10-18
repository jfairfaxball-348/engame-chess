# Research charter — Endgame Chess

## Mission
**Overarching objective (owner, 2026-10-18): proof-based tablebase equivalence.** For each endgame material class, establish by mathematical proof, formalised in Lean, the same knowledge an endgame tablebase such as Syzygy provides: the exact outcome (win / draw / loss, and whether any mate is possible at all) of *every* legal position, and eventually the distance information (moves to mate or to a zeroing move under the 50-move rule).
- **No lookup.** The knowledge must come from general theorems: explicit invariants, strategies, characterisations and bounds that a person can read and Lean can check. It must never come from a stored table of per-position results, or from a proof that merely replays one.
- **Small steps.** The route there is incremental: *small, exact, checked, formally verified* theorems, one defensible result at a time. Each frozen theorem settles a precisely stated slice of a material class. The roadmap tracks how much of each class is settled.
- **No dates.** There is no promised timetable; tractability decides the next step.

## Hard boundaries
- **No tablebases**: do not consult Syzygy, Nalimov, Lomonosov or equivalents, including transcriptions, derived evaluations or databases of resolved positions. Theorems come from explicit definitions, mathematical argument and independently checked formal proof.
- **Tablebase equivalence without tablebase methods.** The goal is to *know what a tablebase knows*, by proof. Exhaustive enumeration, retrograde analysis and per-position certificates are not acceptable as the proof of a tablebase-equivalent claim. They may appear only as supplementary local diagnostics (below).
- An engine or finite simulation cannot certify a theorem. Diagnostic scripts can discover errors, supply finite counterexamples or check examples, provided the source is local and disclosed.
- A known chess truism is a *candidate* until proved in the chosen model.
- Never silently switch meanings of draw, legal move, possible mate, forced mate, stalemate, dead position or position reachability.
- No fabricated novelty. Consult prior art when claiming new discoveries; classical re-proofs are legitimate foundational outputs, but must be labelled classical.
- No unchecked Lean: no `sorry`, `admit`, unexplained axioms, or declarations merely claiming success.
- Freeze only after local proof audit and formal verification, preserving the exact Git source revision and compiler/toolchain details.
- Do not alter a frozen theorem silently; append a versioned supersession/correction with explanation.

## Mathematical lenses
1. Combinatorial game theory (strategy quantifiers, alternating game graphs, termination and non-termination).
2. Metric geometry (Chebyshev, Manhattan, graph and taxicab distances; boundaries and restricted motion).
3. Symbolic logic (quantifiers, invariants, predicates and exact outcome semantics).
4. Piece-movement functions (attack maps, moves and legal transition relations).
5. Graph theory, symmetry, parity and colouring arguments.
6. Any further mathematical domain *as an instrument of a specific small theorem*.

## Proof pipeline
`PROPOSED → LOCAL_VERIFIED → FORMAL_VERIFIED → FROZEN`.
The detailed gates, required artifacts and exceptional correction procedure are in [PROOF_PROTOCOL.md](PROOF_PROTOCOL.md).

## Complexity policy
Piece count is the default first ordering, *not* a permanent restriction. Later rungs may instead be organised by information, branching factor, geometric constraints, forcing strategy, rule dependence, pawn promotion or depth of reasoning. Choose the next tractable proof, not the most impressive-sounding claim.

## Session convention
One principal claim or prerequisite per session; explicit deliverables, checkable closeout, full next-session prompt. Research sessions are `S001`, `S002`, …; bootstrap `S000` is administrative. A pasted or linked numbered session prompt authorises its execution. If a claim fails, document the failure and preserve the candidate for refinement.
