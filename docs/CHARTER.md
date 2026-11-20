# Research charter — Endgame Chess

## Mission
**Ultimate ambition (owner, 2026-10-18; explicitly aspirational): ultra-weakly solve chess as a draw.** Seek a rigorous mathematical proof, ideally formalised in Lean, that the *standard initial position* of chess has game-theoretic value **draw** under an explicitly specified, complete rules model. This would prove that White and Black can each avoid a forced loss against optimal opposition. It does **not** require identifying which moves guarantee the result, publishing a playable perfect strategy or building a chess-playing oracle. The owner's preference is for a mathematical discovery rather than a move-by-move "cheat code". **No such proof is claimed to exist; chess being drawn is a research hypothesis, not an established fact.**

**Major operational milestone (owner, 2026-11-20; clarifies the 2026-10-18 wording): Endgame Outcome Parity, ultimately through seven pieces.** The project does *not* aim to reproduce every feature of Syzygy or any other tablebase. For each covered material class it proves, by general mathematics formalised in Lean, the correct game-theoretic outcome of every legal position within the stated rules domain:
- win / draw / loss under the specified rules, distinguishing unconditional wins/losses from cursed wins/blessed losses where relevant;
- dead versus live positions;
- actual winning and drawing/holding strategies, with every legal opponent response accounted for;
- rule-aware treatment of the 50-move rule, repetition and the associated automatic draws (staged; see the [parity target](#parity-target-hard-boundary-owner-2026-10-29) and [roadmap](ROADMAP.md));
- sufficient progress bounds or termination measures proving the claimed outcome.

The proofs must explain *why* the outcomes hold, through geometric conditions, invariants, strategy arguments, induction and other general structure.
- **DTM and DTZ are not objectives.** Exact (optimal) distance to mate and distance to zeroing are permanently outside the research objectives, including the seven-piece ambition: not completion gates, not future milestones. Sufficient bounds remain mandatory: mate within 98 plies certifies a win before the draw threshold, while the minimum is unnecessary; in pawn endings, prove that progress or a resetting move can be forced in time, not its optimal distance. Frozen exact-distance results (e.g. EC-T0049) stay valid and intact.
- **No lookup.** The knowledge must come from general theorems: explicit invariants, strategies, characterisations and bounds that a person can read and Lean can check. It must never come from a stored table of per-position results, or from a proof that merely replays one.
- **A formula, not a strategy.** Where no human-sized strategy exists, the obligation still stands. The outcome must be captured by a closed mathematical characterisation proved in Lean, never by enumeration (owner, 2026-10-18; see ROADMAP).
- **Small steps.** The route there is incremental: *small, exact, checked, formally verified* theorems, one defensible result at a time. Each frozen theorem settles a precisely stated slice of a material class. The roadmap tracks how much of each class is settled.
- **No dates.** There is no promised timetable; tractability decides the next step.

## Hierarchy of ambitions (not a change of session priorities)
- **Distant ambition:** prove the single initial-position value of standard chess is a draw (*ultra-weak* solving). A value proof is enough even if it is non-constructive; no practical move recommendation is required.
- **Major intermediate milestone:** Endgame Outcome Parity through seven pieces, through general characterisations and Lean proofs, with no tablebase lookup and no optimal-distance (DTM/DTZ) obligation.
- **Near-term execution:** tackle the live mathematical obligation, prove sound lemmas, formalise in Lean and freeze theorems when truly verified. There are no mandatory numbered sessions or duplicate administrative freeze stages. Do not substitute a speculative initial-position attack for the active endgame target.

Terminology matters: an *ultra-weak* solution establishes the theoretical value of the initial position; a *weak* solution additionally provides a way to achieve that value from the initial position against every opponent response; a *strong* solution determines correct play or values for all legal positions. Proving a draw value logically implies that non-losing strategies exist, but an ultra-weak proof need not construct them. Local constructive forcing-strategy lemmas remain valid and often necessary intermediate mathematics; the ultimate ambition simply does not demand an end-user chess-playing algorithm.

A full-game claim will require a precisely pinned rules and terminal-outcome model, including relevant history-dependent draw conditions. The present endgame rules kernel deliberately omits some such information; it must not be mistaken for an already complete model of initial-position game value. Progress through endgames **does not imply** the ultimate conjecture or guarantee that endgame techniques generalise.

## Parity target (hard boundary, owner 2026-10-29)
The class-completion target is **guaranteed outcome for every position**, and no more. For every legal position of the class (either side to move, 50-move counter at zero, no prior game history), prove:
- **WDL50** (required): the result with perfect play under the 50-move rule (win / cursed win / draw / blessed loss / loss), with an actual forcing or holding argument. Mate, stalemate and dead positions are as in the rules kernel.
- **A proved move bound** for wins, sufficient to settle the 50-move rule.

**Exact DTZ50/DTM** (the optimal "mate in n") is not an objective (see Mission). It is not a class-completion gate and is not a reason to delay the next class.

This fresh-root gate is the class-completion target for KPK and does not change while KPK is open. For it, also not required: arbitrary nonzero incoming clocks, incoming repetition histories, the draw-claim procedure (current/intended claims), positions with castling rights, or a broader FIDE-adjudication bridge. Results already proved beyond this boundary (history-aware, clock-banded, castling-aware theorems) are kept intact as frozen evidence. For this gate the rules model need only be faithful for the semantics above.

**Owner, 2026-11-20:** these history-aware obligations are reopened, for the two- and three-piece classes only, as the separate **Three-Piece Full Rules Closure** milestone, which begins only after KPK is complete and frozen (see [roadmap](ROADMAP.md)). There, arbitrary legally reachable incoming clocks and repetition histories are mandatory, not optional, and the rules model must be audited for those mechanisms.

## Hard boundaries
- **No tablebases**: do not consult Syzygy, Nalimov, Lomonosov or equivalents, including transcriptions, derived evaluations or databases of resolved positions. Theorems come from explicit definitions, mathematical argument and independently checked formal proof.
- **Outcome parity without tablebase methods.** The goal is to *know the outcomes a tablebase records*, by proof. Exhaustive enumeration, computed retrograde tables and per-position certificates are not acceptable as the proof of an outcome-parity claim, even when the computation runs inside Lean: they do not generalise to the next material class. They may appear only as supplementary local diagnostics (below). Induction on distance over explicitly described geometric regions is mathematics, not enumeration.
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

## Working convention
Work continuously on the current material-class obligation, including during local laptop sessions. Session numbers, one-claim-per-session limits, formal closeouts, session ledgers, reports and full next-session prompts are no longer required. Preserve substantive proof/counterexample findings in the relevant mathematical source; retain the frozen Lean and ledger safeguards described in [PROOF_PROTOCOL.md](PROOF_PROTOCOL.md). The optional [live work note](../NEXT_SESSION.md) is updated only when the obligation actually changes.
