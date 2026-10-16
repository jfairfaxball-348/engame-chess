# NEXT SESSION — S004: K+B vs K is a dead position (EC-C002, Gate L only)

**Owner instruction:** Execute this S004 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C002 is `PROPOSED`. Do not treat this prompt as evidence it is solved.

## Objective
Produce a complete, locally verified proof that every game-arisen position with White K+B versus Black K (and, by colour symmetry, Black K+B versus White K) is dead under FIDE 2023 Article 5.2.2. Stop at Gate L: no Lean in this session, no ledger change.

## Non-negotiable scope
- 8×8 orthodox chess; material exactly {K, B} versus {K}; FIDE 2023, https://handbook.fide.com/chapter/E012023 (Arts. 1.2, 1.4.1, 3.1–3.10, 3.5 bishop, 5.2.2).
- No tablebases, no engine oracles, no tablebase-derived evidence.
- **Checks are possible here.** The bishop can check the lone king. Do *not* reuse EC-T0001's "no check" argument. Mate must be excluded by the geometry of the lone king's escape squares and of what a bishop and king can cover, not by the absence of check.
- Distinguish no-possible-mate (`Dead`) from no-forced-mate. Distinguish `Arisen` from local admissibility. Note that the bishop can also be the *mated* side's opponent only; the lone king can never mate.

## Required work
1. **Model** (extend `docs/FOUNDATIONS.md` without editing the frozen K-vs-K layer's meaning):
   - bishop attack with obstruction: diagonal rays stopped by the first occupied square, where the kings are the only possible blockers;
   - KBK states: squares of WK, WB, BK, plus the side to move;
   - legal moves for each side;
   - captures: the lone king may capture an unprotected bishop.
2. **Material class closed under legal moves:** KBK ∪ KK. After a bishop capture the position is K vs K, so use **EC-T0001** (`theorems/frozen/EC-T0001/v1.md`) as a cited lemma for that branch rather than re-proving it.
3. **Core lemma:** no KBK position (legal: side not to move is not in check) is checkmate of the lone king.
   - In any check by the bishop, the lone king has a flight square, or can capture the bishop, or the position is illegal.
   - Analyse corners and edges explicitly: the lone king in a corner, a bishop check along the long diagonal, and the White king covering squares.
   - Use colour-complex arguments: a bishop controls only squares of one colour, and adjacent squares along a rank or file alternate colour.
4. **Invariance** under every legal step, including the capture branch, then path induction over finite series, giving `Dead`.
5. **Hostile audit** `audits/EC-C002_KBK.md`:
   - board edges and corners;
   - king obstruction of bishop rays;
   - discovered-check impossibility;
   - illegal positions where both kings are in check;
   - the capture branch;
   - zero-length paths;
   - both sides to move.
6. **Diagnostic** `scripts/kbk_diagnostic.py`, written independently from the movement rules (supplementary only), with a unit test. Enumerate all legal KBK placements with both sides to move and confirm 0 checkmates, plus closure into KBK ∪ KK.
7. Write `proofs/EC-C002_KBK.md`, self-contained. Set EC-C002 to `LOCAL_VERIFIED` only if no gap survives; otherwise keep `PROPOSED` and state the gap precisely.
8. `theorems/LEDGER.csv` unchanged.

## Lean forward note (for S005, not now)
One module per theorem. A KBK formalisation goes in a new module (e.g. `formal/EndgameChess/KBK.lean`). It may import `EndgameChess.KK`, but **must not edit it** (EC-T0001 is frozen). Shared board definitions, if needed, go in a new module.

## Closeout
Write `sessions/S004_KBK_PROOF.md` and add a `sessions/SESSION_LEDGER.md` row. Record:
- changes;
- what was proved, tested and conjectured, as separate lists;
- checks actually run;
- base and result SHAs;
- candidate status;
- ledger effect (none).

Install the next prompt in full: S005 = Lean formalisation of EC-C002 if Gate L passes, otherwise a targeted remedial S004. Then commit, push and merge to `main`.
