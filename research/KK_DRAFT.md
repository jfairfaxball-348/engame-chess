# EC-C001 — King versus king is a dead position

> **Superseded (S001, 2026-10-16):** the audited proof is [proofs/EC-C001_KK.md](../proofs/EC-C001_KK.md) with audit [audits/EC-C001_KK.md](../audits/EC-C001_KK.md). This draft is kept unchanged below as the historical S000 record; note it reads the 2023 Art. 3.8 as forbidding moves to attacked squares, which the 2023 text does not say (the prohibition comes from 3.9.2).

**Status (historical, S000):** PROPOSED / draft argument, *not yet audited or Lean-verified*.  
**Rules:** FIDE 2023, Articles 1.4–1.5, 3.8–3.10, 5.2.2. https://handbook.fide.com/chapter/E012023  
**Scope:** Ordinary 8×8 chess, exactly one white king and one black king, no other pieces, and a position that has arisen legally in a game.

## Proposed formal mathematical claim
For any KK-admissible configuration `p=(w,b,t)` with `d∞(w,b)≥2`, *every* finite core-legal move path beginning at `p` ends in a KK-admissible configuration with neither king in check. In particular no such path ends in checkmate. It follows that `p` is a dead position and, if it arises in an actual game, the game is immediately drawn under Article 5.2.2.

## Draft lemma chain (to be adversarially checked)

**L1: Attack metric.** For two distinct squares `u,v`, a king on `u` attacks `v` iff `d∞(u,v)=1`. This follows from the stipulated king-movement and board model.

**L2: Safety.** In any admissible two-king configuration `d∞(w,b)≥2`, neither king attacks the other. As each player has exactly one piece, neither king is in check.

**L3: Step closure.** A core-legal king move moves one king to a neighbouring on-board square and cannot finish with adjacent kings or king capture. Consequently `StepKK(p,q)` and KK-admissibility of `p` imply KK-admissibility of `q`. The total material (two kings only) remains unchanged.

**L4: Finite path closure.** Induction on the number of `StepKK` transitions using L3 gives that all states reachable through any finite core-legal sequence are KK-admissible.

**L5: No checkmate.** L2 and L4 show that at no reachable state is any king in check. Because check is a necessary condition for checkmate, no reachable state can be a checkmate state. This does not require proving existence of a legal next move in every state.

**L6: Rule consequence.** By the quantifier in FIDE 5.2.2 ('any series of legal moves'), the result of L5 implies neither side can possibly checkmate. An actual game reaching such a position is drawn immediately by the dead-position rule, not merely after repetition, agreement, fifty/seventy-five moves, or both sides choosing to do nothing.

## Obligations for S001
1. Verify L1 against precise FIDE rules, noting attack vs moving into check.
2. Ensure the definition of KK-admissible is *sufficient for local KK safety*, not asserted equal to global starting-position reachability.
3. Verify closure with correct turn order and no king capture.
4. Confirm path-length-zero and terminal-rule cases do not make the argument circular.
5. Separate mathematically impossible checkmate from the rule conclusion 'immediate draw'.
6. Search for counterexamples at corners and edges; record *how* checks were performed, not just 'none'.
7. Produce a final self-contained locally audited proof or report gaps; do not grant `LOCAL_VERIFIED` prematurely.

## Known conceptual trap
A common proof says 'the kings can move forever; hence a draw'. That neither proves the impossibility of mating nor accurately explains the immediate dead-position rule. Our route must prove **invariant impossibility of checkmate**, then apply the draw rule.
