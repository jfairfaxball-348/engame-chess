# Endgame Chess — proof-first mathematical research

A deliberately incremental research programme in **mathematical chess endgames**. The aim is not to solve chess or announce a grand conjecture. It is to build a growing corpus of narrowly stated, independently checked and eventually **Lean 4-formalised theorems**, beginning with **king versus king**.

## Intellectual approach

We study endgames using combinatorial game theory, metric and discrete geometry, symbolic logic, graph theory, invariant reasoning, finite-state semantics, piece-movement functions, and further methods when useful. **Do not use Syzygy, other endgame tablebases, tablebase-derived positions, or tablebase evaluations** as evidence, discovery input or proof.

The sequence is **define precisely → prove on paper/local reasoning → adversarially audit → formalise in Lean → compile/check axioms → freeze proof → enter immutable theorem-ledger record → advance by one small step**.

## First rungs

1. **K vs K**: why no legal continuation can produce checkmate, and why FIDE's dead-position rule implies an immediate draw.
2. **K+B vs K**: prove a separate, explicitly quantified dead-position result.
3. **K+N vs K**: likewise, with knight movement modelled directly.
4. Move to cases where mating positions exist, forcing and non-forcing distinctions matter, or pawns introduce promotion and history.

These are **research targets, not yet project-certified theorems**. In particular, “no possible mate,” “no forced mate” and “draw under the rules” are different predicates; never conflate them.

## Scope and source of rules

Classical chess, 8×8 board, ordinary FIDE piece movement and legal positions. Working rule reference: [FIDE Laws of Chess, effective 1 January 2023](https://handbook.fide.com/chapter/E012023), especially Articles 1.4–1.5, 3.8–3.10 and 5.2.2. A theorem explicitly states which rule edition and model it uses. Rules about time forfeiture, resignation, claims and clock play are separate layers, never smuggled into a geometric statement.

## Repository navigation

- [Research charter](docs/CHARTER.md)
- [Precise mathematical model](docs/FOUNDATIONS.md)
- [Proof → formalisation → freeze protocol](docs/PROOF_PROTOCOL.md)
- [Methods and non-goals](docs/METHODS.md)
- [Incremental research ladder](docs/ROADMAP.md)
- [Candidate register](research/CANDIDATES.md)
- [First mathematical proof draft, **unverified**](research/KK_DRAFT.md)
- [Authoritative frozen-theorem ledger](theorems/LEDGER.csv)
- [Session record](sessions/SESSION_LEDGER.md)
- [Installed next-session prompt](NEXT_SESSION.md)
- [Lean staging directory](formal/README.md)

## Scientific status

**Bootstrap only.** No theorem has yet passed the complete local-proof, Lean and freeze gates. The K-vs-K argument is a draft awaiting an explicit hostile audit; the ledger is empty on purpose.

Research can grow in *conceptual* complexity as well as piece count: board boundaries, metrics, colour complexes, opposition, zugzwang, reachability, bounded strategies, pawn structure, promotions, and rule-dependent draw conditions.

## Contributing or running sessions

Read the charter and proof protocol first. Follow the active full prompt in `NEXT_SESSION.md`. Never mark a result as frozen because it is well known, because a chess engine agrees, or because a finite sample supports it. Frozen records have exact statements, independently checked derivations, compiling formal proof sources, reproducible build information and immutable Git identifiers.
