# EC-C009 — Clock-free forced-mate semantics and soundness

Gate L proof, S024 (2026-10-19). Classical finite reachability-game reasoning; no novelty claim. Board and legal moves are the project's FIDE 2023 kernel. No clocks, repetition, resignation, time loss or draw claims occur in this game.

## Definitions
For named winner σ, let Gσ(q) mean q.turn = opposite(σ) and q is checkmate. A mate already on the board is a win in zero plies. Let D(q) mean kernel deadness, and L(q,r) kernel legality. Define predicates Fₙ recursively:

- F₀(q) := Gσ(q).
- Fₙ₊₁(q) := Gσ(q), or all of the following: q is not dead; and either (q.turn = σ and some legal successor satisfies Fₙ), or (q.turn = opposite(σ), at least one legal successor exists, and every legal successor satisfies Fₙ).
- ForceMate(σ,q) := ∃n, Fₙ(q).

The budgets are upper bounds in **plies**. They do not demand that every branch use the same number of moves. The base case is included at every level. A position with legal successors cannot be checkmate, so the move clauses cannot continue from mate. Stalemate has no successors and is not the goal. Dead positions cannot use a move clause and cannot be the goal, since zero-length reachability would contradict deadness. Thus play stops at checkmate, stalemate and deadness. Infinite non-mating play is not a forcing win.

This is the finite-rank inductive reachability attractor, defined directly by uniform natural-number bounds. We do not introduce a separate strategy object or claim a strategy/rank equivalence theorem. Its existential and universal clauses themselves prescribe the exact finite-horizon game quantifiers: recursively choose a move on σ's turn; cover every opponent reply within the remaining budget. No stored position table is used. Eventual-winning strategies in arbitrary infinitely branching games are outside this definition; our chess move relation is finitely branching, but that equivalence is not needed or claimed here.

## Proofs

**Monotonicity.** Fₙ implies Fₙ₊₁. Induct on n. A goal remains a goal. In a nonterminal winning state, apply the induction hypothesis to the chosen successor or to every legal successor, leaving the turn, nondeadness and nonempty-reply evidence unchanged. Iteration gives arbitrary larger budgets.

**Soundness.** Fₙ(q) implies a finite L-path from q to a position satisfying Gσ. Induct on n. The goal uses the zero-length path. In the choosing case use the witnessed legal successor and its inductive path. In the defender case choose one successor from the explicitly nonempty set; its universal continuation gives the inductive path. Prefix the legal move. Therefore ForceMate implies not dead.

**Terminal soundness.** If q has no legal successor, ForceMate(σ,q) iff Gσ(q): at every positive budget the move clauses contradict no-successor. Hence stalemate and checkmate of σ are not forcing wins for σ. Defender checkmate is a zero-ply win.

**Dead-reply obstruction.** Suppose q.turn = opposite(σ) and some legal move leads to a dead r. A goal at q contradicts that legal move. A choose clause has the wrong turn. A defend clause requires Fₙ(r), which contradicts soundness and deadness. Thus ForceMate(σ,q) is false, even if q is live.

**Finite branching and one-step rules.** Given a finite list of successors each having some finite bound, combine their bounds by addition (or maximum), using monotonicity. The kernel explicitly lists all legal successors in `legalPositions`, so pointwise forcing of every legal reply has a common finite bound. For a nonempty defending node this proves the one-step defending rule. Its nondeadness follows by prefixing the move to any forcing successor. The choosing rule follows similarly from one forcing successor. This proves the one-step closure needed to reduce weak-to-move KRK to the strong-to-move theorem; it does not introduce a separate strategy representation.

## KRK negative witness
White Kh8, Rb3, Black Ka2, Black to move (no flags). Kxb3 and Ka1 are legal. Kxb3 leaves K vs K and is dead by EC-T0003. Ka1 leaves KRK with White to move after a legal move, so it is live by EC-T0007. Consequently the starting position is live, yet White cannot force mate by the dead-reply obstruction. Black has the explicit holding choice Kxb3, after which neither colour can force mate. Global reachability from the initial position is not asserted. All move and material facts for this fixed example are to be checked in the kernel; its general negative implication is proved symbolically above.

## Candidate boundaries
The general soundness and terminal lemmas are EC-C009. The full KRK optimal-play characterisation remains EC-C011, PROPOSED: first establish the strong-to-move theorem under correct legality assumptions; then handle checkmate, stalemate, any optional rook capture, and remaining weak-to-move states separately. No FIDE 50/75-move WDL, repetition WDL, full Syzygy WDL/DTZ or standard-chess result follows.
