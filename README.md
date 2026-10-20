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

**After S070.** Thirty-seven frozen theorem bundles (not thirty-six solved material classes). K+R vs K dead/live and its clock-free strong-turn forcing and weak-turn terminal/capture classification are frozen. Full FIDE rule/distance parity remains open.
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
- S034: EC-C022 frozen as [EC-T0020](theorems/frozen/EC-T0020/v1.md) after a new exact-source Gate Z build. All three interface/proof modules and both declarations are frozen; scope remains abstract.
- S035: **EC-C023 FORMAL_VERIFIED**: stored initial-rooted raw moves, exact append/prefix retention, raw step soundness and complete reply lifting, with kernel endpoint origin. [Paper](proofs/EC-C023_RAW_TRACE_APPEND.md), [evidence](sessions/evidence/S035/README.md). This is raw trace data, not no-earlier-terminal FIDE admissibility.
- S036: **EC-C024 FORMAL_VERIFIED**: a raw halfmove fold, legal pawn/capture reset-event equivalence, castling empty-destination fact, exact append update and global/one-step ply bounds. [Paper](proofs/EC-C024_RAW_HALFMOVE_FOLD.md), [evidence](sessions/evidence/S036/README.md). No complete FIDE admissibility/adjudication or numerical KRK bound.
- S037: EC-C023/024 frozen separately as [EC-T0021](theorems/frozen/EC-T0021/v1.md) and [EC-T0022](theorems/frozen/EC-T0022/v1.md), after two new sequential exact-source Gate Z builds. All ten declarations and source/import identities checked; no formal source changed. [Evidence](theorems/frozen/VERIFICATION-S037/README.md), [closeout](sessions/S037_FREEZE_RAW_TRACE_CLOCK.md).
- S038: **EC-C025 FORMAL_VERIFIED**: raw multi-step clock growth along actual stored-trace extensions, including resets, with the exact same state at zero plies. [Paper](proofs/EC-C025_RAW_CLOCK_EXTENSION_BOUND.md), [evidence](sessions/evidence/S038/README.md). Gate Z pending; no sufficient-budget lifting or numerical KRK bound.
- S039: EC-C025 frozen as [EC-T0023](theorems/frozen/EC-T0023/v1.md) after a new exact-source Gate Z build and complete axiom audit. All prior source/records unchanged.
- S040: **EC-C026 FORMAL_VERIFIED**: under an explicit clock(s)+n<100 hypothesis, every actual k≤n prefix and EVERY prospective raw step at k<n has clock<100. [Paper](proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md), [evidence](sessions/evidence/S040/README.md). Gate Z pending; repetition/FIDE claim semantics and numerical KRK remain open.
- S041: EC-C026 frozen as [EC-T0024](theorems/frozen/EC-T0024/v1.md) after new exact-source Gate Z, 69 jobs and 273 allowed reports. Prior sources/records unchanged.
- S042: **EC-C027 FORMAL_VERIFIED**: occurrence counting for a fixed arbitrary key map with decidable equality and exact append law; root/full history retained even on reset. [Paper](proofs/EC-C027_RAW_KEY_OCCURRENCES.md), [evidence](sessions/evidence/S042/README.md). Gate Z pending; this is not a FIDE repetition-key theorem.
- S043: EC-C027 frozen as [EC-T0025](theorems/frozen/EC-T0025/v1.md) after new exact-source Gate Z, 71 jobs and 274 allowed reports. Full prior source/records preserved.
- S044: **EC-C028 FORMAL_VERIFIED**: actual legal ep event and noncomputable effective target, none iff no legal witness and some dst iff a witness targets dst. [Paper](proofs/EC-C028_EFFECTIVE_EP_TARGET.md), [evidence](sessions/evidence/S044/README.md). Gate Z pending; no complete FIDE repetition-key result.
- S045: EC-C028 frozen as [EC-T0026](theorems/frozen/EC-T0026/v1.md) after new exact-source Gate Z (73 jobs, 275 allowed reports), with all prior source/records preserved.
- S046: **EC-C029 FORMAL_VERIFIED**: an actual legal source pawn changing file into an empty destination is exactly the defined LegalEP event; raw marker/flank recovered from kernel legality. [Paper](proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md), [evidence](sessions/evidence/S046/README.md). Gate Z pending; no ep-normalization or full FIDE key theorem.
- S047: EC-C029 frozen as [EC-T0027](theorems/frozen/EC-T0027/v1.md) after new exact-source Gate Z (74 jobs, 276 allowed reports), all prior source/records preserved. Owner requested stopping at this closeout.
- Next (paused; not started): S067, direct quantitative KRK strategy attack under the [short-term closure roadmap](docs/KRK_COMPLETION.md). EC-C039 freeze remains backlog. Concrete FIDE correspondence, strategy-specific repetition certificates and numerical KRK/outcome/distance coverage remain open.

Research can grow in *conceptual* complexity as well as piece count: board boundaries, metrics, colour complexes, opposition, zugzwang, reachability, bounded strategies, pawn structure, promotions, and rule-dependent draw conditions.

## Contributing or running sessions

Session workflow rule (see [AGENTS.md](AGENTS.md); `CLAUDE.md` imports it): every session commits, pushes and merges its work into `main`.

Read the charter and proof protocol first. Follow the active full prompt in `NEXT_SESSION.md`. Never mark a result as frozen because it is well known, because a chess engine agrees, or because a finite sample supports it. Frozen records have exact statements, independently checked derivations, compiling formal proof sources, reproducible build information and immutable Git identifiers.

- S048: EC-C030 **FORMAL_VERIFIED**, raw ep-marker irrelevance outside EP shape, including full played Position equality. [Paper](proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md), [evidence](sessions/evidence/S048/README.md). S049 separate freeze next; consecutive sessions resumed by owner.

- S049: EC-C030 frozen as [EC-T0028](theorems/frozen/EC-T0028/v1.md), separate exact-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S049/README.md).

- S050: EC-C031 **FORMAL_VERIFIED**, effective ep normalization preserves Boolean legality for every move and full endpoints of legal moves. [Paper](proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md), [evidence](sessions/evidence/S050/README.md). No full FIDE repetition-key result.

- S051: EC-C031 frozen as [EC-T0029](theorems/frozen/EC-T0029/v1.md), both normalization modules immutable; separate exact-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S051/README.md).

- S052: EC-C032 **FORMAL_VERIFIED**, equal full normalized keys have equal Boolean legality and full legal endpoints. [Paper](proofs/EC-C032_NORMALIZED_KEY_CONGRUENCE.md), [evidence](sessions/evidence/S052/README.md).

- S053: EC-C032 frozen as [EC-T0030](theorems/frozen/EC-T0030/v1.md), both key modules immutable; separate exact-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S053/README.md).

- S054: EC-C033 **FORMAL_VERIFIED**, current count after append queries the NEW endpoint key in the OLD full history, plus one. [Paper](proofs/EC-C033_NORMALIZED_KEY_OCCURRENCES.md), [evidence](sessions/evidence/S054/README.md).

- S055: EC-C033 frozen as [EC-T0031](theorems/frozen/EC-T0031/v1.md), both count modules immutable; separate own-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S055/README.md).

- S056: EC-C034 **FORMAL_VERIFIED**, explicit root and EVERY legal intended-move bounds exclude raw clock/repetition thresholds. [Paper](proofs/EC-C034_RAW_THRESHOLD_CERTIFICATE.md), [evidence](sessions/evidence/S056/README.md). Raw bookkeeping, not certified FIDE claims.

- S057: EC-C034 frozen as [EC-T0032](theorems/frozen/EC-T0032/v1.md), both raw threshold modules immutable; separate own-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S057/README.md).

- S058: EC-C035 **FORMAL_VERIFIED**, exact current/ALL intended-child raw threshold exclusion iff. [Paper](proofs/EC-C035_EXACT_RAW_THRESHOLD_EXCLUSION.md), [evidence](sessions/evidence/S058/README.md).

- S059: EC-C035 frozen as [EC-T0033](theorems/frozen/EC-T0033/v1.md), complete characterization module immutable; separate own-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S059/README.md).

- S060: EC-C036 **FORMAL_VERIFIED**, raw mate-first classifier ongoing iff nondead/legal successor/clock<150/count<5. [Paper](proofs/EC-C036_RAW_ENDPOINT_CLASSIFIER.md), [evidence](sessions/evidence/S060/README.md).

- S061: EC-C036 frozen as [EC-T0034](theorems/frozen/EC-T0034/v1.md), raw endpoint definitions/ongoing characterization immutable. [Evidence](theorems/frozen/VERIFICATION-S061/README.md).

- S062: EC-C037 **FORMAL_VERIFIED**, exact stopped-history append guards and EVERY legal-reply lifting, including terminal children. [Paper](proofs/EC-C037_STOPPED_HISTORY_LIFTING.md), [evidence](sessions/evidence/S062/README.md). Gate Z pending; raw classifier-relative history only.

- S063: EC-C037 frozen as [EC-T0035](theorems/frozen/EC-T0035/v1.md), stopped-history definitions/append and full-reply lifting immutable. [Evidence](theorems/frozen/VERIFICATION-S063/README.md).

- S064: EC-C038 **FORMAL_VERIFIED**, concrete RAW stopped-history Layer with EVERY legal reply, including terminal children, and same-budget certificate projection. [Paper](proofs/EC-C038_RAW_STOPPED_HISTORY_LAYER.md), [evidence](sessions/evidence/S064/README.md). [KRK completion obligations](docs/KRK_COMPLETION.md) remain explicit; stop before KQK.

- S065: EC-C038 frozen as [EC-T0036](theorems/frozen/EC-T0036/v1.md), concrete RAW Layer and same-budget projection immutable. [Evidence](theorems/frozen/VERIFICATION-S065/README.md).

- S066: EC-C039 **FORMAL_VERIFIED**, same-budget raw rule-mate lifting under clock+n<100 and count<3 on EVERY actual raw prefix through n. [Paper](proofs/EC-C039_RAW_SUFFICIENT_BUDGET_LIFTING.md), [evidence](sessions/evidence/S066/README.md). Strong sufficient certificate only; no general KRK history/numeric witness or full outcome coverage.

S067: [EC-C040 quantitative KRK paper](proofs/EC-C040_KRK_QUANTITATIVE_BOUND.md)
and [separate same-agent audit](audits/EC-C040_KRK_QUANTITATIVE_PAPER.md) give a
508-ply clock-free ceiling, LOCAL_VERIFIED only. S068 formalises it; no rule-aware
coverage or frozen-bundle change. Consecutive sessions resumed by owner request.

S068: EC-C040 508-ply KRK bound is FORMAL_VERIFIED; [fresh exact-source evidence](sessions/evidence/S068/README.md). Gate Z remains separate; 36 bundles frozen, rule-aware outcomes and exact distance still open.

S069: [EC-T0037](theorems/frozen/EC-T0037/v1.md) freezes the explicit 508-ply KRK strategy. 37 frozen bundles; complete KRK rule-aware coverage and exact distances remain open. S070 returns directly to strategy-specific repetition safety.

S070: EC-C041 key-simple minimal-budget KRK strategy FORMAL_VERIFIED; [evidence](sessions/evidence/S070/README.md). All legal weak replies retained; new-path key uniqueness does not handle old incoming occurrences or complete FIDE outcomes. 37 frozen bundles; S071 returns to actual history lifting.
