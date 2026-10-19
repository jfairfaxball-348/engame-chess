# Endgame Chess — proof-first mathematical research

A deliberately incremental research programme in **mathematical chess endgames**.

**Ultimate ambition (not a proved claim): ultra-weakly solve chess as a draw.** The hoped-for discovery is a rigorous mathematical proof, ideally formalised in Lean, that the standard initial position of chess has game-theoretic value **draw** under a precisely specified, complete rules model. An *ultra-weak* solution would establish that neither side can force a win against optimal defence, **without needing to supply perfect moves or an executable playing strategy**. The purpose is to discover a mathematical truth, not to give players a move-by-move "cheat code". Chess is not currently proved to be drawn, and the project's endgame results do not establish this claim.

**Major operational milestone (unchanged): proof-based parity with complete seven-piece Syzygy tablebases.** For each covered endgame material class, the programme aims to prove mathematically, and formalise in Lean, what the tables know: the exact outcome of every legal position, and eventually their distance information. It does this through general theorems (invariants, strategies, characterisations, bounds), **never through lookup** of stored per-position results. The incremental proof-and-freeze programme and the installed next session remain unchanged. See [docs/CHARTER.md](docs/CHARTER.md) and [docs/ROADMAP.md](docs/ROADMAP.md).

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

**After S033.** Nineteen frozen theorem bundles (not nineteen solved material classes). K+R vs K dead/live and its clock-free strong-turn forcing and weak-turn terminal/capture classification are frozen. Full FIDE rule/distance parity remains open.
- [EC-T0001](theorems/frozen/EC-T0001/v1.md) (K vs K) and [EC-T0002](theorems/frozen/EC-T0002/v1.md) (K+B vs K) were proved over bespoke models.
- [EC-T0003](theorems/frozen/EC-T0003/v1.md) and [EC-T0004](theorems/frozen/EC-T0004/v1.md) strengthen them over the general FIDE rules kernel (`formal/EndgameChess/Rules/`): every K vs K or K+B vs K position produced by *any* legal move, including a capture from larger material, is dead, and every arisen one is drawn immediately under the named rule encoding `Rule5_2_2` (Art. 5.2.2).
- What remains trusted: assumption A1 and the kernel bridge [docs/RULES_KERNEL.md](docs/RULES_KERNEL.md). The project owner reviewed the kernel rules on 2026-10-18 and found no issues. Manifests frozen before that date still say the review is open; they are not edited (frozen-record rule).
- [EC-T0005](theorems/frozen/EC-T0005/v1.md) (K+N vs K) was stated over the kernel from the start: paper proof S011, Lean S012 (`Rules/KNK.lean`), frozen S013.
- S014: rung 4 (K+R vs K) opened with *possible* mate. EC-C007 (`LOCAL_VERIFIED`): a K+R vs K position where the lone king must take the rook (or is stalemated) is dead, so Art. 5.2.2 can end a game with a rook on the board. The converse EC-C008 is `PROPOSED`, with exhaustive diagnostic support.
- S015: EC-C007 formalised in Lean (`Rules/KRK.lean`, `FORMAL_VERIFIED`).
- S016: EC-C007 frozen as [EC-T0006](theorems/frozen/EC-T0006/v1.md).
- S017: EC-C008 partially proved. An explicit cooperative mating route works from every strong-to-move K+R vs K state (simulator); its last three phases are proved; two gaps remain.
- S018–S019: route repaired and the relocation lemma proved. **EC-C008 is `LOCAL_VERIFIED`**: together with EC-T0006, a legal K+R vs K position is dead iff the lone king is to move, it is not checkmate, and every legal move captures the rook. That settles layer L1 for K+R vs K on paper.
- S020: Lean toolchain migrated to v4.35.0, which meets Palomar's minimum. All six frozen theorems were re-verified with identical statements, and v2 manifests were written.
- S021: EC-C008 Lean, part 1. KRK infrastructure over the kernel (attack and check on `krkBoard`, a geometric move model with kernel soundness, reflections F4) and the end-game half (Lemmas M, E, C, W, S) are formalised. EC-C008 stays `LOCAL_VERIFIED`.
- S022: EC-C008 fully formalised (RL-h, RL-f, P1, main theorems). **EC-C008 is `FORMAL_VERIFIED`**: in the kernel, a K+R vs K position with the strong side to move (produced by a legal move) is never dead, and with the lone king to move it is dead iff not checkmate and every legal move captures the rook.
- S023: EC-C008 frozen as [EC-T0007](theorems/frozen/EC-T0007/v1.md) after fresh-clone verification of `a8bc161`. Together with EC-T0006 this completes K+R vs K L1.
- S024: **EC-C009 and EC-C010 FORMAL_VERIFIED**: finite-rank clock-free forcing semantics, the optional-capture obstruction, and a protected rook rank barrier preserved by every legal lone-king reply. Kernel examples distinguish stalemate, wrong-colour mate and blocked rook rays. Full K+R vs K forcing (EC-C011) remains open: safe setup, tempo and strict progress still need proof.
- S025: EC-C009 frozen as [EC-T0008](theorems/frozen/EC-T0008/v1.md), EC-C010 as [EC-T0009](theorems/frozen/EC-T0009/v1.md), after fresh exact-source Gate Z verification.
- S026: **EC-C012/013 FORMAL_VERIFIED**: distant-or-protected rook safety and a four-ply opposed-kings checking phase. Against every defence it either mates at the edge or advances the lone king and returns a safe distant-rook barrier. A four-file margin is proved sufficient; smaller-margin and re-entry failures are kernel-checked.
- S027: EC-C012 frozen as [EC-T0010](theorems/frozen/EC-T0010/v1.md), EC-C013 as [EC-T0011](theorems/frozen/EC-T0011/v1.md), after new fresh exact-source Gate Z verification. The phase requires a four-file rook margin, same-file kings two ranks apart, strong turn and the rook off the lone king's rank; both colours and arbitrary flags. It is a contraction for that family, not general KRK WDL or a repeatable full strategy.
- S028: EC-C014 proves the exact phase-image bounds with legal ancestry and all-reply quantifiers. EC-C015 gives a two-or-four-ply rank contraction from the entire upper band, including a far-file rescue if the raised rook is hanging. These prerequisites are FORMAL_VERIFIED, not frozen; the ledger remains at eleven.
- S029: EC-C016–018 close the lower-band pursuit and continuation gap. `krk_rank_wall_force` proves clock-free forced mate for every exact strong-turn KRK with strong king below a separating rook rank and lone king above it, including every S028 phase image. A direct vertical-entry subfamily also wins. The bounded waiting/pursuit and nested rank/gap induction cover all defences; these results are FORMAL_VERIFIED, not frozen.
- S030: **EC-C011 and EC-C019–021 FORMAL_VERIFIED**. Proved alternating strategy transport, all-axis walls, finite safe setup from every strong-turn legal KRK arrival, and the weak-turn terminal/capture classification. Both colours and arbitrary flags; every legal defence covered. [Proof](proofs/EC-C019_C021_KRK_SAFE_SETUP.md), [evidence](sessions/evidence/S030/README.md).
- S031: **EC-T0012–EC-T0019 FROZEN** after three new fresh exact-source Gate Z builds, covering phase image, upper-band rescue, two-file check, conditional pursuit, unconditional walls, capture/move interface, restricted transport and full clock-free setup/classification. All 62 public declarations checked; source modules unchanged. [Evidence](theorems/frozen/VERIFICATION-S031/README.md), [closeout](sessions/S031_FREEZE_KRK_FORCING.md). Nineteen bundles, not nineteen solved classes.
- S032: [Rule/history and distance specification](research/KRK_RULE_DISTANCE_SPEC.md) completed as design only; EC-C022 remains PROPOSED. Intended-move claims and mate/draw precedence are explicit; no additional theorem or frozen bundle.
- S033: **EC-C022 FORMAL_VERIFIED**: an abstract rule-layer mate certificate projects to frozen clock-free forcing with the identical ply budget, provided every raw legal reply lifts and ongoing moves are sound/nondead. [Paper](proofs/EC-C022_RULE_LAYER_PROJECTION.md), [evidence](sessions/evidence/S033/README.md). This does not instantiate the concrete FIDE history layer.
- Next: S034, separate Gate Z freeze of that precise abstract interface and two projection results. Concrete histories/claims, sufficient-budget lifting and numerical KRK distances remain open.

Research can grow in *conceptual* complexity as well as piece count: board boundaries, metrics, colour complexes, opposition, zugzwang, reachability, bounded strategies, pawn structure, promotions, and rule-dependent draw conditions.

## Contributing or running sessions

Session workflow rule (see [AGENTS.md](AGENTS.md); `CLAUDE.md` imports it): every session commits, pushes and merges its work into `main`.

Read the charter and proof protocol first. Follow the active full prompt in `NEXT_SESSION.md`. Never mark a result as frozen because it is well known, because a chess engine agrees, or because a finite sample supports it. Frozen records have exact statements, independently checked derivations, compiling formal proof sources, reproducible build information and immutable Git identifiers.
