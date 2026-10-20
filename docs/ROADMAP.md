# Roadmap

## Distant horizon: ultra-weakly solve chess
**Ultimate ambition (owner, 2026-10-18; unproved):** establish by a rigorous mathematical argument, ideally formalised in Lean, that standard chess from its initial position is a theoretical **draw**: \(V(S_0)=0\), under a complete, explicitly fixed rules model. This is an *ultra-weak* target: prove the position's value, not a playable perfect-move strategy or a "cheat code". The result is not known and must not be inferred from endgame progress. Whether the methods below can generalise as far as the initial position is an open research question.

## Major operational milestone (unchanged): proof-based seven-piece tablebase parity
The existing objective (owner, 2026-10-18; [CHARTER](CHARTER.md)) is to know, **by proof and without lookup**, what the complete up-to-seven-piece Syzygy tablebases know, one material class at a time. For a class this means four layers, in increasing strength. This is still the active roadmap; the numbered next-session prompt and near-term priorities are unchanged:

| Layer | Question for every legal position of the class | Tablebase analogue |
|---|---|---|
| L1 Dead / live | Can any checkmate still occur (`DeadK`)? | (FIDE 5.2.2; not stored by Syzygy) |
| L2 Outcome | Win, draw or loss with best play, under an explicit rule model (with or without the 50-move rule) | WDL |
| L3 Strategy | An explicit winning or holding strategy, with a proof that it works against every defence | (implicit in DTZ/DTM) |
| L4 Distance | Exact or bounded moves to mate or to a zeroing move | DTM / DTZ |

**Coverage of the 3-piece classes (Syzygy's smallest tables):**

| Class | L1 | L2 | L3 | L4 |
|---|---|---|---|---|
| K vs K | **done** (EC-T0001/0003: every position dead) | done (draw) | n/a | n/a |
| K+B vs K | **done** (EC-T0002/0004) | done (draw) | n/a | n/a |
| K+N vs K | **done** (EC-T0005) | done (draw) | n/a | n/a |
| K+R vs K | **done, frozen**: dead ⇔ lone king to move, not mate, every legal move captures the rook (EC-T0006 + EC-T0007, S023) | Clock-free forcing classified, frozen EC-T0019; FIDE rule-aware outcomes open | Clock-free forcing proved and frozen; rule-aware strategy open | Numeric distance / DTZ open |
| K+Q vs K | open | open | open | open |
| K+P vs K | open | open | open | open |

A class counts as **tablebase-equivalent** in this programme only when L2 is proved for *every* legal position of the class, by a general argument, and formalised in Lean. Exhaustive scripts may confirm a statement but never prove it.

**L2 prerequisites:** EC-T0008/0009 freeze the forcing framework and protected-rank confinement. S027 froze distant/protected safety as EC-T0010 and the four-file opposed-kings checking phase as EC-T0011. The phase covers both colours and arbitrary flags, but its final kings need not remain opposed.

S028 proved the actual phase-image bounds (EC-C014) and bounded upper-band rank advance/rescue (EC-C015). S029 closes lower-band pursuit and the continuation invariant for a broader separated-rank family: **EC-C018 proves ForceMate from exact strong-turn KRK with S.rank<R.rank<W.rank**, including every S028 image. EC-C016/017 supply two-file checking and bounded pursuit. EC-C014–018 subsequently passed S031 Gate Z as EC-T0012–EC-T0016. The pursuit interface remains explicitly conditional; the wall result has no assumed winning-continuation hypothesis.

S030 closes arbitrary-arrival safe setup and the necessary alternating strategy/axis transport. **EC-C011 and EC-C019–021 were FORMAL_VERIFIED in S030 and FROZEN in S031 as EC-T0017–EC-T0019**: every strong-turn exact KRK legal arrival forces mate; a weak turn forces mate iff it is actual mate, or has nonempty replies with no KK capture. The proof includes threatened rooks, changing axes, same-rank/back-rank setup and stalemate controls, with every legal defence covered. [Paper](../proofs/EC-C019_C021_KRK_SAFE_SETUP.md), [Gate F evidence](../sessions/evidence/S030/README.md). S031 froze the complete verified development as EC-T0012–EC-T0019, with three new exact-source Gate Z builds and 62 public declarations checked. Nineteen frozen bundles are not nineteen solved classes. S032 specifies the separate clock/repetition and numeric distance layer; S033 verified its first generic projection bridge; no full FIDE WDL/DTZ, seven-piece or initial-position result is marked solved.

S032 supplied the [rule/distance specification](../research/KRK_RULE_DISTANCE_SPEC.md): full legal history, halfmove updates, effective-en-passant repetition keys, current/intended draw claims, automatic draw and mate precedence, and a first mate-bound target in plies. S033 proves **EC-C022, subsequently frozen as EC-T0020 in S034**: a generic same-budget projection under explicit ongoing move-soundness, coverage of EVERY raw legal reply and nondeadness hypotheses. Its existential forcing corollary retains the same uniform bound. [Paper](../proofs/EC-C022_RULE_LAYER_PROJECTION.md), [Gate F evidence](../sessions/evidence/S033/README.md). S034 froze all three complete interface/proof modules and both declarations after a new exact-source Gate Z run. Twenty bundles are not twenty solved material classes. S035 verifies **EC-C023 FORMAL_VERIFIED**: concrete initial-rooted raw move data, ordered append retention, full raw-reply lifting/soundness and kernel endpoint origin. [Paper](../proofs/EC-C023_RAW_TRACE_APPEND.md), [evidence](../sessions/evidence/S035/README.md). It is not no-earlier-terminal FIDE admissibility or a full Layer instance; S037 subsequently froze it as EC-T0021. S036 verifies **EC-C024 FORMAL_VERIFIED**: the raw halfmove fold, legal reset-event equivalence, castling empty-destination fact, exact append update and structural/one-step ply bounds. [Paper](../proofs/EC-C024_RAW_HALFMOVE_FOLD.md), [evidence](../sessions/evidence/S036/README.md). All S035/frozen sources are unchanged; no material-count equivalence or complete FIDE adjudication is claimed. S037 froze EC-C023/024 separately as EC-T0021/0022 after two new sequential exact-source Gate Z builds (59/66 jobs; 265/271 allowed axiom reports). All prior Lean sources and records remain unchanged. Twenty-two bundles are not twenty-two solved classes. S038 formally verifies **EC-C025**: raw multi-step clock growth along actual trace extensions, including resets and exact-state retention at zero plies. [Paper](../proofs/EC-C025_RAW_CLOCK_EXTENSION_BOUND.md), [evidence](../sessions/evidence/S038/README.md). S039 froze it as EC-T0023 after a new exact-source Gate Z build (68 jobs; 272 allowed reports). Twenty-three frozen bundles, no new solved material class. S040 formally verifies **EC-C026**, the explicit-hypothesis prefix/prospective-ply clock certificate ([paper](../proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md), [evidence](../sessions/evidence/S040/README.md)); S041 freezes it as EC-T0024 after new exact-source Gate Z (69 jobs, 273 allowed reports). Twenty-four bundles; S042 formally verifies **EC-C027**, generic full-history key occurrence counting and exact append law ([paper](../proofs/EC-C027_RAW_KEY_OCCURRENCES.md), [evidence](../sessions/evidence/S042/README.md)); S043 freezes this as EC-T0025 after new exact-source Gate Z (71 jobs, 274 allowed reports). Twenty-five bundles; S044 formally verifies **EC-C028**, legality-filtered en-passant availability/effective-target specification ([paper](../proofs/EC-C028_EFFECTIVE_EP_TARGET.md), [evidence](../sessions/evidence/S044/README.md)); S045 freezes this as EC-T0026 after new exact-source Gate Z (73 jobs, 275 allowed reports). Twenty-six bundles; S046 formally verifies **EC-C029**, exact kernel LegalEP characterization ([paper](../proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md), [evidence](../sessions/evidence/S046/README.md)); S047 freezes this as EC-T0027 after new exact-source Gate Z (74 jobs, 276 allowed reports). Twenty-seven bundles. S048 formally verified EC-C030, ordinary ep-marker irrelevance outside raw EP shape, including full played Position equality ([paper](../proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md), [evidence](../sessions/evidence/S048/README.md)); owner resumed consecutive sessions, S049 froze it as EC-T0028 after a new exact-source Gate Z check; 28 bundles. S050 formally verified EC-C031: effectiveEP normalization preserves Boolean legality and full legal-move endpoints ([paper](../proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md), [evidence](../sessions/evidence/S050/README.md)); S051 froze this as EC-T0029 after new own-source Gate Z, 29 bundles; S052 formally verified EC-C032, normalized-key legal-move/full-legal-endpoint congruence ([paper](../proofs/EC-C032_NORMALIZED_KEY_CONGRUENCE.md), [evidence](../sessions/evidence/S052/README.md)); S053 separate freeze next. No FIDE repetition key is claimed; no numerical KRK bound, repetition certificate or sufficient-budget lifting follows. Concrete FIDE instantiation, sufficient-budget lifting, history invariants, holding/determinacy and numerical KRK distances remain open. No new class outcome or rule-aware KRK distance is claimed.

### What full Syzygy equivalence obliges (assessment, 2026-10-18)
1. **Rule model for L2/L4.** Syzygy's WDL distinguishes wins from "cursed wins" (wins that the 50-move rule turns into draws), and its DTZ counts moves to a zeroing move. The kernel omits the half-move clock and repetition (`RULES_KERNEL.md`, modelling choice 3). It needs a **clock layer** (Art. 9.3/9.6) before any L2-with-50-move or L4 claim.
2. **Per-class theorems, at every layer, for every legal position.** Syzygy covers all material classes with up to 7 pieces: 5 three-piece classes and, by the usual counts, about 30 four-piece and about 110 five-piece classes, with hundreds more at 6–7. The K vs K base case is not a table.
3. **A method that scales.** One bespoke paper proof plus one bespoke Lean proof per class will not reach 5–7 pieces. Needed: reusable theorems, such as dead-position criteria (colour complexes, blocked positions), forcing-strategy templates with potential functions for termination, reduction lemmas (a capture or promotion leads to an already-settled class), and symmetry.
4. **Owner decision (2026-10-18): every result needs a mathematical form, even where no human-sized strategy exists.** For every ending with fewer than 8 pieces, the guaranteed outcome must be proved via a closed mathematical characterisation: a formula or predicate over the position that decides win/draw/loss (and later distance), proved in Lean to agree with the game. That is the point of the repo: work backwards from simple endings, remove the human and the lookup element, and leave a formula plus a machine-checked proof.
   - Per-position enumeration does **not** count, *even if kernel-checked*: a `decide` over every position of a class, or a stored certificate per position, is lookup in another form.
   - Finite `decide` checks remain acceptable for **bounded local lemmas inside a general proof**, e.g. a fixed small configuration, and for non-vacuity witnesses.
   - Whether compact characterisations exist for the hardest 6–7 piece endings is itself an open research question. Finding them is the programme's long-run content.

**Palomar registry compatibility (checked 2026-10-18).** Palomar (palomar-registry.org, Lean FRO / ICARM) registers Lean-verified results. Its current requirements conflict with this repo as it stands:
- **toolchain ≥ `v4.35.0-rc2`** (`PalomarSubmission/toolchains.json`). **Done in S020:** the repo now pins `v4.35.0`, and all frozen theorems were re-verified;
- **every** `.lean` file in the repository must use the Lean `module` system; none of ours do yet;
- `Challenge.lean`, `Solution.lean`, `comparator.json` and `formalization.yaml` are needed;
- a licence file is needed at the repository root; there is none yet;
- only the standard axioms are allowed, and no `native_decide`. **We already comply with this.**

The remaining port is the module system: it edits every module, frozen ones included. Under `docs/PROOF_PROTOCOL.md` that is a new versioned record (re-verification of all theorems, superseding manifest versions), not an in-place edit. It is scheduled as a dedicated migration session.

**Where we are:**
- **Three-piece classes** (KQK, KRK, KBK, KNK, KPK):
  - KBK and KNK are settled at L1 (dead), which implies L2 (draw), with no L4 content; frozen.
  - KRK has L1 complete and frozen (EC-T0006 + EC-T0007, S023), and clock-free forcing fully classified and frozen (EC-T0019, S031). Rule-aware L2 and numerical L4 remain open. A live position need not be a forced win: the lone king may have an optional rook capture. The classification includes terminal mate, stalemate and any legal KK capture; S032 specifies the remaining rule/distance layer; S033 verified only the generic projection bridge; its concrete FIDE instantiation remains open.
  - KQK and KPK are open. KPK is the first genuinely hard L2 class, because of promotion, opposition and stalemate.
- No full four-piece or larger class is proved in this project. Bundle counts do not measure class completion or a percentage of Syzygy coverage. The audited, owner-reviewed rules kernel and reusable deadness, reachability and forcing results support the next rule-aware obligations.

## Incremental ladder (revisable)

All listed statements are *targets*, not certified theorems.

| Rung | Material / topic | Precise question | Principal difficulty |
|---|---|---|---|
| 0 | Movement/logic primitives | Board, king attacks, legal KK states and steps | Definitions faithfully represent rules |
| 1 | K vs K | Is every admissible KK position dead? | Simple invariant and FIDE connection — `LOCAL_VERIFIED` in S001; `FORMAL_VERIFIED` in S002 (Lean 4.34.1); **frozen as EC-T0001** (S003) |
| 2 | K+B vs K | Is every admissible single-bishop ending dead? | Sliding attack geometry, obstruction — `LOCAL_VERIFIED` in S004; `FORMAL_VERIFIED` in S005; **frozen as EC-T0002** (S006) |
| K | Rules kernel (owner decision 2026-10-16) | One general Lean encoding of FIDE Art. 3 (all pieces, castling, en passant, promotion, check) that agrees with `KK.LegalKK` / `KBK.Step`; `Arisen` as reachability; Art. 5.2.2 as a named rule definition | Closes trust gaps G1/G2 and makes G3 explicit for EC-T0001/2. S007 (model — **done**), S008 (agreement — **done**), S009 (reachability + 5.2.2 rule — **done**; candidates EC-C005/006), S010 (frozen as **EC-T0003/EC-T0004**) |
| 3 | K+N vs K | Is every admissible single-knight ending dead? | Knight's discrete attack geometry — Gate L (S011), Gate F over the kernel (S012); **frozen as EC-T0005** (S013) |
| 4 | K+R vs K | First: which K+R vs K positions are dead (possible mate)? EC-C007 (forced capture / stalemate ⇒ dead) `LOCAL_VERIFIED` S014, `FORMAL_VERIFIED` S015, **frozen as EC-T0006** S016; converse EC-C008 **frozen as EC-T0007** S023 (L1 complete). Clock-free forcing classified and frozen as EC-T0019 (S031); clock/repetition and numeric distance remain open. | Not every K+R vs K position is live (e.g. a forced rook capture); then strategy `∃` vs `∀`, finite descent |
| 5 | K+Q vs K | Can a simple metric potential prove forcing? | Boundary/corner control |
| 6 | Four-piece cases | Contrast possibility, force and dead position | Same material, different geometric types |
| 7 | Pawn endings | Promotion, opposition, tempo and zugzwang | State/history and richer transitions |
| Open | Geometry/invariants | New local lemmas on distances, parity, legal regions | Small publishable deductions may appear |

Do not skip a simpler prerequisite solely because another result is famous. New branches may be indexed by geometry, strategy depth, board symmetry or logic rather than raw piece count. Complexity ladder does not impose fixed deadlines.

### Initial working questions
- Can legality of a king-only position be characterised by `d∞≥2` without accidental claims about global reachability?
- Can deadness be proven as an invariant of all core legal continuations?
- What minimal extension to the attack relation is required for bishops/knights?
- Which very small endings exhibit 'mate possible but not forceable', making the distinction explicit?
