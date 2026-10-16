# NEXT SESSION — S005: Lean 4 formalisation of EC-C002 (K+B vs K dead position)

**Owner instruction:** Execute this S005 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C002 is `LOCAL_VERIFIED` only. Do not treat this prompt as evidence that any Lean proof exists.

## Objective
Formalise `proofs/EC-C002_KBK.md` faithfully in a **new module** `formal/EndgameChess/KBK.lean` (namespace `EndgameChess.KBK`), and reach Gate F (`FORMAL_VERIFIED`) only if every Gate F check in `docs/PROOF_PROTOCOL.md` passes. **Do not freeze.** `theorems/LEDGER.csv` stays unchanged.

## Constraints
- `formal/EndgameChess/KK.lean` is **frozen** (EC-T0001). Import it (`import EndgameChess.KK`) and reuse `Square`, `dInf`, `Adjoining`, `KKState`, `Admissible`, `LegalKK`, `not_inCheck_of_admissible` and `admissible_of_legal_step`, but **never edit it**. If a shared definition is missing, put it in a new module.
- Same toolchain `leanprover/lean4:v4.34.1`, core only. No `sorry`, `admit`, custom `axiom`, `unsafe` or `native_decide`.
- Lean checks the model. The FIDE bridge (A1; the bishop reading of 3.1.2 + 3.2 + 3.5; the move-set identification) stays in prose.
- Verify only what is an obligation (`AGENTS.md`): the new module and its importers. Do not re-verify EC-T0001 beyond what `lake build` does incrementally.

## Required work
1. **Definitions:**
   - `Side` (strong/weak, or reuse `Colour`).
   - `KBKState` (strong king, bishop, weak king, side to move).
   - `onDiag`.
   - `bishopAttacks` with obstruction: `q` is on a diagonal of `X` and all squares strictly between are empty, the occupancy being the two kings.
   - `inCheck` for both sides.
   - `LKBK`.
   - Legal moves for both sides as a relation that mirrors the FIDE conditions: the strong king, the bishop (diagonal, unobstructed, not onto an own piece, not capturing the king, mover not in check afterwards), and the weak king (including the capture of the bishop).
   - A combined position type `Pos := kbk KBKState | kk KKState`, with a step relation that embeds `LegalKK` on the `kk` side and maps a bishop capture to `kk`.
   - `Checkmate`, `Reach` (inductive), and `Dead` over `Pos`.
2. **Theorems** mirroring B0–B5:
   - `colour_of_bishopAttacks` (B1a);
   - `colour_orth_neighbour` (B1b);
   - `kings_apart_of_LKBK` and `strong_not_inCheck` (B0′);
   - `weak_has_move_of_inCheck` (B2, the key lemma; prove it by the `h`/`v` construction, not by enumeration);
   - `closed_of_step` (B3; the `kk` branch uses EC-T0001's `admissible_of_legal_step`);
   - `closed_of_reach` (B4);
   - `not_checkmate_of_closed` (B5);
   - **`dead_of_LKBK`** (main);
   - `LKBK_of_last_move_legal`, for a predecessor within the model.
3. **Non-vacuity:**
   - prove a KBK stalemate exists (e.g. Ka8 / Kb6 + Bc7) — this is not a mate;
   - prove a bishop check exists;
   - prove `Checkmate` is satisfiable somewhere in the model, or explain why the definitions make it impossible and why that is still meaningful. For example, in an illegal state where the side not to move is in check.
4. **Checks:**
   - add the new main declarations to `formal/AxiomCheck.lean`;
   - `lake build`;
   - `#print axioms` (expect `[propext, Classical.choice, Quot.sound]` or fewer);
   - the forbidden-token grep;
   - a clean-checkout build of the proof commit;
   - record the outputs verbatim.
5. **Fidelity audit** `audits/EC-C002_KBK_LEAN.md`:
   - a definition and theorem map;
   - surrogate checks: obstruction modelled, both sides' moves complete, the capture branch present, turn handling, and that `Dead` quantifies over all paths;
   - residual prose bridge.
6. **Status:** EC-C002 → `FORMAL_VERIFIED` only if steps 4–5 pass, recording the proof-source commit SHA, toolchain, declaration names and axioms. Otherwise keep `LOCAL_VERIFIED` and state the blocker.

## Closeout
Write `sessions/S005_KBK_LEAN.md` and add a `sessions/SESSION_LEDGER.md` row. Record:
- changes;
- checks actually run;
- base SHA and proof-source SHA;
- CI evidence if observed;
- candidate status;
- ledger effect (none).

Install the next prompt in full. If Gate F passed: S006 = freeze EC-C002 as EC-T0002 (Gate Z; cite the S005 proof commit). Otherwise: a remedial S005. Then commit, push and merge to `main`.
