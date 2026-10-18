# Endgame Chess — proof-first mathematical research

A deliberately incremental research programme in **mathematical chess endgames**.

**Overarching objective: proof-based tablebase equivalence.** For each endgame material class, the programme aims to prove mathematically, and formalise in Lean, everything an endgame tablebase such as Syzygy knows: the exact outcome of every legal position, and eventually its distance information. It does this through general theorems (invariants, strategies, characterisations, bounds), **never through lookup** of stored per-position results. See [docs/CHARTER.md](docs/CHARTER.md) and the coverage table in [docs/ROADMAP.md](docs/ROADMAP.md).

The route is a growing corpus of narrowly stated, independently checked, **Lean 4-formalised theorems**, one small step at a time, beginning with **king versus king**.

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

**After S016.** Six frozen theorems.
- [EC-T0001](theorems/frozen/EC-T0001/v1.md) (K vs K) and [EC-T0002](theorems/frozen/EC-T0002/v1.md) (K+B vs K) were proved over bespoke models.
- [EC-T0003](theorems/frozen/EC-T0003/v1.md) and [EC-T0004](theorems/frozen/EC-T0004/v1.md) strengthen them over the general FIDE rules kernel (`formal/EndgameChess/Rules/`): every K vs K or K+B vs K position produced by *any* legal move, including a capture from larger material, is dead, and every arisen one is drawn immediately under the named rule encoding `Rule5_2_2` (Art. 5.2.2).
- What remains trusted: assumption A1 and the kernel bridge [docs/RULES_KERNEL.md](docs/RULES_KERNEL.md). The project owner reviewed the kernel rules on 2026-10-18 and found no issues. Manifests frozen before that date still say the review is open; they are not edited (frozen-record rule).
- [EC-T0005](theorems/frozen/EC-T0005/v1.md) (K+N vs K) was stated over the kernel from the start: paper proof S011, Lean S012 (`Rules/KNK.lean`), frozen S013.
- S014: rung 4 (K+R vs K) opened with *possible* mate. EC-C007 (`LOCAL_VERIFIED`): a K+R vs K position where the lone king must take the rook (or is stalemated) is dead, so Art. 5.2.2 can end a game with a rook on the board. The converse EC-C008 is `PROPOSED`, with exhaustive diagnostic support.
- S015: EC-C007 formalised in Lean (`Rules/KRK.lean`, `FORMAL_VERIFIED`).
- S016: EC-C007 frozen as [EC-T0006](theorems/frozen/EC-T0006/v1.md).
- S017: EC-C008 partially proved. An explicit cooperative mating route works from every strong-to-move K+R vs K state (simulator); its last three phases are proved; two gaps remain.
- S018–S019: route repaired and the relocation lemma proved. **EC-C008 is `LOCAL_VERIFIED`**: together with EC-T0006, a legal K+R vs K position is dead iff the lone king is to move, it is not checkmate, and every legal move captures the rook. That settles layer L1 for K+R vs K on paper.
- Next: S020, Lean formalisation of EC-C008 (multi-session).

Research can grow in *conceptual* complexity as well as piece count: board boundaries, metrics, colour complexes, opposition, zugzwang, reachability, bounded strategies, pawn structure, promotions, and rule-dependent draw conditions.

## Contributing or running sessions

Session workflow rule (see [AGENTS.md](AGENTS.md); `CLAUDE.md` imports it): every session commits, pushes and merges its work into `main`.

Read the charter and proof protocol first. Follow the active full prompt in `NEXT_SESSION.md`. Never mark a result as frozen because it is well known, because a chess engine agrees, or because a finite sample supports it. Frozen records have exact statements, independently checked derivations, compiling formal proof sources, reproducible build information and immutable Git identifiers.
