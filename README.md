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
- [EC-C001 K-vs-K local proof](proofs/EC-C001_KK.md), its [audit](audits/EC-C001_KK.md), the [Lean formalisation](formal/README.md) and its [fidelity audit](audits/EC-C001_KK_LEAN.md) (`FORMAL_VERIFIED`, not frozen)
- [Superseded S000 draft](research/KK_DRAFT.md)
- [Authoritative frozen-theorem ledger](theorems/LEDGER.csv)
- [Session record](sessions/SESSION_LEDGER.md)
- [Installed next-session prompt](NEXT_SESSION.md)
- [Lean staging directory](formal/README.md)

## Scientific status

**After S006.** Two frozen theorems: **[EC-T0002](theorems/frozen/EC-T0002/v1.md)** (K+B vs K is dead; frozen S006) and **[EC-T0001](theorems/frozen/EC-T0001/v1.md)** (from EC-C001), K vs K is dead, hence a FIDE 5.2.2 draw. It passed Gate L (S001), Gate F (S002; `EndgameChess.KK.dead_of_admissible`, Lean 4.34.1, standard axioms only) and Gate Z (S003). The FIDE-to-model bridge stays in prose (see the manifest's trust boundary). Both manifests list three prose-only trust gaps (move-set fidelity, capture-arisen positions, the 5.2.2 rule step). The rules-kernel track (S007–S009, candidate EC-C004) will close or make them explicit. S007 built kernel K1 (`formal/EndgameChess/Rules/`, bridge [docs/RULES_KERNEL.md](docs/RULES_KERNEL.md)). Next: S008, kernel K2 (agreement).

Research can grow in *conceptual* complexity as well as piece count: board boundaries, metrics, colour complexes, opposition, zugzwang, reachability, bounded strategies, pawn structure, promotions, and rule-dependent draw conditions.

## Contributing or running sessions

Session workflow rule (see [AGENTS.md](AGENTS.md); `CLAUDE.md` imports it): every session commits, pushes and merges its work into `main`.

Read the charter and proof protocol first. Follow the active full prompt in `NEXT_SESSION.md`. Never mark a result as frozen because it is well known, because a chess engine agrees, or because a finite sample supports it. Frozen records have exact statements, independently checked derivations, compiling formal proof sources, reproducible build information and immutable Git identifiers.
