# S004 — K+B vs K dead-position proof (Gate L)

**Date:** 2026-10-16
**Type:** Theorem session (local mathematics only).
**Base revision:** `9e796895ab015f163ee1be18efc86a2d990dcee6` (`main`, S003). CI observed green on the base: Lean run 38903522282 and ledger run 38903522013.
**Result:** the S004 commit on branch `claude/epic-goldberg-mrynfu`, merged to `main`. It does not cite its own SHA.

## Changes
- `proofs/EC-C002_KBK.md` (new). A self-contained proof containing:
  - verbatim FIDE 3.2 and 3.5;
  - lemmas B0 (arisen ⇒ LKBK), B0′ (kings apart; the strong side never in check), B1 (colour complex), **B2** (a checked lone king always has an orthogonal escape), B3 (closure, including the bishop-capture branch into K vs K via EC-T0001), B4 (path induction) and B5 (no checkmate in the class);
  - the theorem, for both orientations, and the 5.2.2 corollary.
- `audits/EC-C002_KBK.md` (new). A hostile audit with 17 attempted falsifications, including a mutation test of the diagnostic.
- `scripts/kbk_diagnostic.py` and `tests/test_kbk_diagnostic.py` (new). An exhaustive enumeration with an independent ray-walking bishop. Supplementary only; no tablebase.
- `docs/FOUNDATIONS.md` gains a K+B vs K layer. `research/CANDIDATES.md` (EC-C002 → `LOCAL_VERIFIED`), `docs/ROADMAP.md` and `README.md` updated.
- `NEXT_SESSION.md`: S005 (Lean formalisation of EC-C002 in a new module) installed.

## Findings, separated
- **Proved (paper, Gate L):** every locally legal K+B vs K configuration, and hence every game-arisen one, is dead in both orientations. FIDE 5.2.2 then gives an immediate draw.
- **Computationally tested (supplement):**
  - all 999,936 placements; 834,456 legal states;
  - 61,320 checks of the lone king, 0 checkmates, 0 checked lone kings without a move;
  - 272 stalemates;
  - 7,938,336 legal moves with 0 closure violations, including 44,352 bishop captures into admissible KK.
  - Mutation (rook-moving piece): 216 mates detected.
- **Conjectured:** none new.
- **Not done:** Lean formalisation (S005); an independent second-reader audit.
- **Correction:** the S004 prompt cited "3.5 bishop". The bishop's move is 3.2; 3.5 is the obstruction rule.

## Checks actually run
- `python3 scripts/kbk_diagnostic.py`: PASSED in 74.4 s (output verbatim in the audit, §2).
- `python3 -m unittest discover -s tests -v`: 14 tests, OK, in 38.5 s. This includes the exhaustive one-orientation KBK run.
- `python3 scripts/validate_ledger.py`: `LEDGER VALID: 1 frozen theorem(s) (structure only)`.
- **Not run:** any Lean build. Not needed: `formal/` is unchanged.

## Status and ledger effect
EC-C002: `PROPOSED → LOCAL_VERIFIED`. `theorems/LEDGER.csv` is unchanged. Frozen theorems: **1** (EC-T0001).

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S005: Lean 4 formalisation of EC-C002 (K+B vs K dead position)
>
> **Owner instruction:** Execute this S005 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C002 is `LOCAL_VERIFIED` only. Do not treat this prompt as evidence that any Lean proof exists.
>
> ## Objective
> Formalise `proofs/EC-C002_KBK.md` faithfully in a **new module** `formal/EndgameChess/KBK.lean` (namespace `EndgameChess.KBK`), and reach Gate F (`FORMAL_VERIFIED`) only if every Gate F check in `docs/PROOF_PROTOCOL.md` passes. **Do not freeze.** `theorems/LEDGER.csv` stays unchanged.
>
> ## Constraints
> - `formal/EndgameChess/KK.lean` is **frozen** (EC-T0001). Import it (`import EndgameChess.KK`) and reuse `Square`, `dInf`, `Adjoining`, `KKState`, `Admissible`, `LegalKK`, `not_inCheck_of_admissible` and `admissible_of_legal_step`, but **never edit it**. If a shared definition is missing, put it in a new module.
> - Same toolchain `leanprover/lean4:v4.34.1`, core only. No `sorry`, `admit`, custom `axiom`, `unsafe` or `native_decide`.
> - Lean checks the model. The FIDE bridge (A1; the bishop reading of 3.1.2 + 3.2 + 3.5; the move-set identification) stays in prose.
> - Verify only what is an obligation (`AGENTS.md`): the new module and its importers. Do not re-verify EC-T0001 beyond what `lake build` does incrementally.
>
> ## Required work
> 1. **Definitions:**
>    - `Side` (strong/weak, or reuse `Colour`).
>    - `KBKState` (strong king, bishop, weak king, side to move).
>    - `onDiag`.
>    - `bishopAttacks` with obstruction: `q` is on a diagonal of `X` and all squares strictly between are empty, the occupancy being the two kings.
>    - `inCheck` for both sides.
>    - `LKBK`.
>    - Legal moves for both sides as a relation that mirrors the FIDE conditions: the strong king, the bishop (diagonal, unobstructed, not onto an own piece, not capturing the king, mover not in check afterwards), and the weak king (including the capture of the bishop).
>    - A combined position type `Pos := kbk KBKState | kk KKState`, with a step relation that embeds `LegalKK` on the `kk` side and maps a bishop capture to `kk`.
>    - `Checkmate`, `Reach` (inductive), and `Dead` over `Pos`.
> 2. **Theorems** mirroring B0–B5:
>    - `colour_of_bishopAttacks` (B1a);
>    - `colour_orth_neighbour` (B1b);
>    - `kings_apart_of_LKBK` and `strong_not_inCheck` (B0′);
>    - `weak_has_move_of_inCheck` (B2, the key lemma; prove it by the `h`/`v` construction, not by enumeration);
>    - `closed_of_step` (B3; the `kk` branch uses EC-T0001's `admissible_of_legal_step`);
>    - `closed_of_reach` (B4);
>    - `not_checkmate_of_closed` (B5);
>    - **`dead_of_LKBK`** (main);
>    - `LKBK_of_last_move_legal`, for a predecessor within the model.
> 3. **Non-vacuity:**
>    - prove a KBK stalemate exists (e.g. Ka8 / Kb6 + Bc7) — this is not a mate;
>    - prove a bishop check exists;
>    - prove `Checkmate` is satisfiable somewhere in the model, or explain why the definitions make it impossible and why that is still meaningful. For example, in an illegal state where the side not to move is in check.
> 4. **Checks:**
>    - add the new main declarations to `formal/AxiomCheck.lean`;
>    - `lake build`;
>    - `#print axioms` (expect `[propext, Classical.choice, Quot.sound]` or fewer);
>    - the forbidden-token grep;
>    - a clean-checkout build of the proof commit;
>    - record the outputs verbatim.
> 5. **Fidelity audit** `audits/EC-C002_KBK_LEAN.md`:
>    - a definition and theorem map;
>    - surrogate checks: obstruction modelled, both sides' moves complete, the capture branch present, turn handling, and that `Dead` quantifies over all paths;
>    - residual prose bridge.
> 6. **Status:** EC-C002 → `FORMAL_VERIFIED` only if steps 4–5 pass, recording the proof-source commit SHA, toolchain, declaration names and axioms. Otherwise keep `LOCAL_VERIFIED` and state the blocker.
>
> ## Closeout
> Write `sessions/S005_KBK_LEAN.md` and add a `sessions/SESSION_LEDGER.md` row. Record:
> - changes;
> - checks actually run;
> - base SHA and proof-source SHA;
> - CI evidence if observed;
> - candidate status;
> - ledger effect (none).
>
> Install the next prompt in full. If Gate F passed: S006 = freeze EC-C002 as EC-T0002 (Gate Z; cite the S005 proof commit). Otherwise: a remedial S005. Then commit, push and merge to `main`.
