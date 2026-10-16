# Incremental roadmap (revisable, not an overarching conjecture)

All listed statements are *targets*, not certified theorems.

| Rung | Material / topic | Precise question | Principal difficulty |
|---|---|---|---|
| 0 | Movement/logic primitives | Board, king attacks, legal KK states and steps | Definitions faithfully represent rules |
| 1 | K vs K | Is every admissible KK position dead? | Simple invariant and FIDE connection — `LOCAL_VERIFIED` in S001; Lean pending |
| 2 | K+B vs K | Is every admissible single-bishop ending dead? | Sliding attack geometry, obstruction |
| 3 | K+N vs K | Is every admissible single-knight ending dead? | Knight's discrete attack geometry |
| 4 | K+R vs K | Does the stronger side possess a forcing strategy? | Strategy `∃` vs `∀`, finite descent |
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
