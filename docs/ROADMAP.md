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
| K+R vs K | Lean-complete: dead ⇔ forced capture or stalemate (EC-T0006 frozen + EC-C008 `FORMAL_VERIFIED`); EC-C008 `FORMAL_VERIFIED` S022 (Lean S021–S022), freeze S023 | open | open | open |
| K+Q vs K | open | open | open | open |
| K+P vs K | open | open | open | open |

A class counts as **tablebase-equivalent** in this programme only when L2 is proved for *every* legal position of the class, by a general argument, and formalised in Lean. Exhaustive scripts may confirm a statement but never prove it.

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
  - KRK has L1 complete on paper (EC-T0006 frozen; EC-C008 `FORMAL_VERIFIED` S022, freeze S023). L2 (strong side wins whenever not dead) and L4 are open.
  - KQK and KPK are open. KPK is the first genuinely hard L2 class, because of promotion, opposition and stalemate.
- **Roughly 2¼ of 5 three-piece classes** at WDL level, and **0 of the 4-piece and larger classes**. As a share of all of Syzygy, this is still well under 1%. The infrastructure (one audited rules kernel, now owner-reviewed, plus reusable deadness and reachability lemmas) is the main asset so far.

## Incremental ladder (revisable)

All listed statements are *targets*, not certified theorems.

| Rung | Material / topic | Precise question | Principal difficulty |
|---|---|---|---|
| 0 | Movement/logic primitives | Board, king attacks, legal KK states and steps | Definitions faithfully represent rules |
| 1 | K vs K | Is every admissible KK position dead? | Simple invariant and FIDE connection — `LOCAL_VERIFIED` in S001; `FORMAL_VERIFIED` in S002 (Lean 4.34.1); **frozen as EC-T0001** (S003) |
| 2 | K+B vs K | Is every admissible single-bishop ending dead? | Sliding attack geometry, obstruction — `LOCAL_VERIFIED` in S004; `FORMAL_VERIFIED` in S005; **frozen as EC-T0002** (S006) |
| K | Rules kernel (owner decision 2026-10-16) | One general Lean encoding of FIDE Art. 3 (all pieces, castling, en passant, promotion, check) that agrees with `KK.LegalKK` / `KBK.Step`; `Arisen` as reachability; Art. 5.2.2 as a named rule definition | Closes trust gaps G1/G2 and makes G3 explicit for EC-T0001/2. S007 (model — **done**), S008 (agreement — **done**), S009 (reachability + 5.2.2 rule — **done**; candidates EC-C005/006), S010 (frozen as **EC-T0003/EC-T0004**) |
| 3 | K+N vs K | Is every admissible single-knight ending dead? | Knight's discrete attack geometry — Gate L (S011), Gate F over the kernel (S012); **frozen as EC-T0005** (S013) |
| 4 | K+R vs K | First: which K+R vs K positions are dead (possible mate)? EC-C007 (forced capture / stalemate ⇒ dead) `LOCAL_VERIFIED` S014, `FORMAL_VERIFIED` S015, **frozen as EC-T0006** S016; converse EC-C008 `PROPOSED`. Then: does the stronger side possess a forcing strategy? | Not every K+R vs K position is live (e.g. a forced rook capture); then strategy `∃` vs `∀`, finite descent |
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
