# NEXT SESSION — S001: Rigorous king-versus-king dead-position theorem

**Owner instruction:** Execute this S001 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Do not treat the prompt as evidence a theorem is already solved.

## Objective
Produce a **complete, locally verified mathematical proof** that any legally arisen two-kings-only position is a dead position, from explicit king movement/attack functions, the Chebyshev geometry of the board, and the exact quantification in the FIDE 2023 dead-position rule. **Stop at the proof-audit gate**: no premature Lean success claims, no ledger freeze.

## Non-negotiable scope
- Standard 8×8 orthodox chess; one White king, one Black king, nothing else; game-arisen legal position.
- No Syzygy, other tablebases, tablebase-derived evidence or engine-oracle evidence.
- Use movement functions, finite paths, invariance and logic; do not merely cite the familiar chess fact.
- Distinguish local admissibility from reachability from the 32-piece initial position; distinguish **no possible mate** from **no forced mate**; distinguish FIDE's immediate dead-position draw from repetition or fifty/seventy-five-move procedures.
- Cite https://handbook.fide.com/chapter/E012023 with relevant article numbers.

## Required work
1. Audit and, if necessary, repair `docs/FOUNDATIONS.md`: coordinates, Chebyshev metric, king attack relation, on-board moves, turn, legal KK states, core legal transition, checks, checkmate, reachable paths and dead position.
2. Prove and write explicit lemmas for: non-adjacent kings in admissible states; no check in any admissible KK state; invariance of only-two-kings material and king separation under **every** legal step; finite-path closure by induction; impossibility of checkmate on any finite continuation.
3. Interpret FIDE Article 5.2.2 carefully and derive the immediate draw for a game-arisen KK position. Explain the counterfactual move graph used in the proof even though FIDE play has already ended.
4. Attack the proof: check board corners/edges, both side-to-move options, zero-length path, king capture, adjacent illegal kings, error in mate quantifiers, and any mismatch between attack and movement relations. Use independent small scripts only as diagnostic supplements; no tablebases.
5. Produce a self-contained local proof `proofs/EC-C001_KK.md` plus a distinct audit record `audits/EC-C001_KK.md` with attempted falsifications and any remaining assumptions.
6. If and only if no gap survives, update candidate EC-C001 to `LOCAL_VERIFIED`. If a gap remains, keep `PROPOSED` and state it precisely.
7. Keep `theorems/LEDGER.csv` empty: **theorem freeze requires Lean success in a later session**.

## Closeout
Record S001 changes, exact repository revision, claims and checks made/not made, candidate status, and next installed session. If gate L passes, install a full S002 prompt to begin faithful Lean 4 formalisation with pinned toolchain. If not, install a full targeted remedial prompt. Include the next prompt in full in the session closeout, not just a link. No inflated novelty claim.
