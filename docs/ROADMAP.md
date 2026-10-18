# Roadmap

## North star: proof-based tablebase equivalence
The overarching objective (owner, 2026-10-18; [CHARTER](CHARTER.md)) is to know, **by proof and without lookup**, what an endgame tablebase knows, one material class at a time. For a class this means four layers, in increasing strength:

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
| K+R vs K | partial: dead ⇐ forced capture or stalemate (**EC-T0006**); converse EC-C008 `PROPOSED` | open | open | open |
| K+Q vs K | open | open | open | open |
| K+P vs K | open | open | open | open |

A class counts as **tablebase-equivalent** in this programme only when L2 is proved for *every* legal position of the class, by a general argument, and formalised in Lean. Exhaustive scripts may confirm a statement but never prove it.

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
