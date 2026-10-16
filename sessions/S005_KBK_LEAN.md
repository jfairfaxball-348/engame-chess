# S005 — Lean 4 formalisation of EC-C002 (Gate F)

**Date:** 2026-10-16
**Type:** Theorem session (formal verification).
**Base revision:** `65bcfad08f36d0722e5cc466ceed2cce06ac0111` (`main`, S004). Ledger CI was observed green on the base (run 38905082599).
**Proof-source commit:** `15610256c9588e2bb5e0c19b035bbfd4437b2e31` (branch `claude/epic-goldberg-mrynfu`, merged to `main`). This closeout lives in a later commit.

## Changes
- `formal/EndgameChess/KBK.lean` (new; SHA-256 `c668e0c0…95c6d7`). It imports the frozen `EndgameChess.KK`, which is unchanged (SHA-256 `4843459c…09b1a0`, matching EC-T0001). It defines:
  - `Side`, `KBKState`, `onDiag`, `between`, `bishopAttacks` (king obstruction) and `kingsOcc`;
  - `weakInCheck`, `strongInCheck`, `LKBK`, `toKK` and `Pos`;
  - `Step` with five constructors, including the bishop capture into K vs K;
  - `Mated`, `Reach`, `Dead`, `Closed` and `col`.

  It proves B1a/B1b, B0′, **B2 `weak_has_move_of_inCheck`** (explicit orthogonal-escape construction), `admissible_of_capture`, B3–B5, **`dead_of_LKBK`**, `dead_of_closed`, `LKBK_of_step`, `dead_of_step`, and the non-vacuity results `bishop_check_exists`, `stalemate_exists` and `mated_satisfiable`.
- `formal/EndgameChess.lean` imports the new module. `formal/AxiomCheck.lean` gains 16 KBK `#print axioms` lines and 2 `#check`s.
- `.github/workflows/lean-build.yml`: the axiom gate now accepts any subset of the standard axioms (some KBK lemmas need fewer). Tested locally on real output (passes) and on a `Lean.ofReduceBool` line (fails).
- `audits/EC-C002_KBK_LEAN.md`: fidelity audit, including a `between`-vs-ray-walking cross-check (35,840 diagonal pairs, 0 mismatches).
- `research/CANDIDATES.md`, `docs/ROADMAP.md`, `README.md`, `formal/README.md` and `sessions/SESSION_LEDGER.md` updated. `NEXT_SESSION.md`: S006 installed.

## Findings, separated
- **Formally proved (Lean, model level):** every locally legal K+B vs K configuration is `Dead` over the K+B vs K / K vs K move graph, in both orientations. So is every such configuration produced by an in-model legal move. A checked lone king always has a legal move.
- **Prose only:**
  - A1;
  - the bishop reading of 3.1.2 + 3.2 + 3.5;
  - the identification of `Step` with the FIDE-legal moves;
  - general B0 (capture predecessors from larger material);
  - the 5.2.2 consequence.
- **Not done:** independent second-reader audits.

## Checks actually run
- Fresh `git clone` from GitHub, checked out at `15610256c9588e2bb5e0c19b035bbfd4437b2e31`, with no `.lake`. `cd formal && lake build` exited 0:
```
✔ [2/5] Built EndgameChess.KK (2.7s)
✔ [3/5] Built EndgameChess.KBK (12s)
✔ [4/5] Built EndgameChess (249ms)
Build completed successfully (5 jobs).
```
- `lake env lean AxiomCheck.lean` in that clean checkout, verbatim (EC-C002 part):
```
'EndgameChess.KBK.dead_of_LKBK' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.dead_of_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.dead_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.LKBK_of_step' does not depend on any axioms
'EndgameChess.KBK.weak_has_move_of_inCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.colour_of_bishopAttacks' depends on axioms: [propext, Quot.sound]
'EndgameChess.KBK.colour_orth_neighbour' depends on axioms: [propext, Quot.sound]
'EndgameChess.KBK.kings_apart_of_LKBK' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.strong_not_inCheck_of_LKBK' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.closed_of_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.closed_of_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.not_mated_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.admissible_of_capture' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.bishop_check_exists' depends on axioms: [propext, Quot.sound]
'EndgameChess.KBK.stalemate_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KBK.mated_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
@EndgameChess.KBK.dead_of_LKBK : ∀ {p : EndgameChess.KBK.KBKState},
  EndgameChess.KBK.LKBK p → EndgameChess.KBK.Dead (EndgameChess.KBK.Pos.kbk p)
@EndgameChess.KBK.dead_of_step : ∀ {p q : EndgameChess.KBK.KBKState},
  EndgameChess.KBK.Step (EndgameChess.KBK.Pos.kbk p) (EndgameChess.KBK.Pos.kbk q) →
    q.sk ≠ q.bs ∧ q.sk ≠ q.wk ∧ q.bs ≠ q.wk → EndgameChess.KBK.Dead (EndgameChess.KBK.Pos.kbk q)
```
  EC-T0001's 12 lines are unchanged: `[propext, Classical.choice, Quot.sound]`. The axiom gate (subset regex) passes.
- Forbidden-token grep over `formal/**/*.lean`, excluding `.lake`: no matches.
- `python3 -m unittest discover -s tests`: 14 tests OK. `python3 scripts/validate_ledger.py`: `LEDGER VALID: 1 frozen theorem(s) (structure only)`.
- Toolchain: Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`), Lake 5.0.0-src+5045d00.
- **Remote CI (observed):** `Lean build (EC formal proofs)` run 38907468354 on the proof commit `15610256` itself: conclusion **success**. https://github.com/jfairfaxball-348/engame-chess/actions/runs/38907468354

## Status and ledger effect
EC-C002: `LOCAL_VERIFIED → FORMAL_VERIFIED`.
- Proof commit `15610256c9588e2bb5e0c19b035bbfd4437b2e31`.
- Toolchain `leanprover/lean4:v4.34.1`.
- Declaration `EndgameChess.KBK.dead_of_LKBK`.
- Axioms ⊆ `[propext, Classical.choice, Quot.sound]`.

`theorems/LEDGER.csv` is unchanged. Frozen theorems: **1**.

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S006: Freeze EC-C002 as EC-T0002 (Gate Z)
>
> **Owner instruction:** Execute this S006 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C002 is `FORMAL_VERIFIED` (S005). Do not treat this prompt as evidence that a freeze has happened.
>
> ## Objective
> Freeze EC-C002 as **EC-T0002** per `docs/PROOF_PROTOCOL.md` Gate Z, citing the S005 proof-source commit **`15610256c9588e2bb5e0c19b035bbfd4437b2e31`**. Use `theorems/frozen/EC-T0001/v1.md` as the template. Do not change the mathematics or `formal/EndgameChess/KBK.lean` / `KK.lean`.
>
> ## Required work
> 1. **Re-verify (only this theorem's obligation).** In a fresh clone at `15610256c9588e2bb5e0c19b035bbfd4437b2e31`, with `leanprover/lean4:v4.34.1`, run:
>    - `cd formal && lake build`;
>    - `lake env lean AxiomCheck.lean` (every `EndgameChess.KBK.*` report must be a subset of `[propext, Classical.choice, Quot.sound]` or "does not depend on any axioms");
>    - the forbidden-token grep.
>
>    Record each SHA-256: `KBK.lean` must be `c668e0c044cf17caa74ad8a75cfdeb0b758e3ccd5b0956ffde88cec2c895c6d7`, and `KK.lean` must still be `4843459ca26af93e15e5894a9f32183d46f8c554132e81051c1c21140509b1a0`. On any mismatch, stop: no freeze, and install a remedial prompt.
> 2. **Drift check.** `git diff 15610256 HEAD -- formal/EndgameChess/` must be empty. Documentation-only changes elsewhere in `formal/` are fine; justify each one.
> 3. **CI evidence.** Use the GitHub tools to look up the `Lean build (EC formal proofs)` run on the proof commit or on `main`, with an identical `formal/EndgameChess/`. Record its ID, URL and conclusion, or write "not observed".
> 4. **Manifest** `theorems/frozen/EC-T0002/v1.md`, with the same sections as EC-T0001:
>    - statement and scope (both orientations; FIDE 2023 Arts 1.2, 1.4.1, 3.1–3.2, 3.5, 3.8–3.10, 5.2.2);
>    - the verbatim `#check` output of `dead_of_LKBK` and `dead_of_step`;
>    - the dependency on EC-T0001 (lemmas used: `admissible_of_legal_step`, `not_inCheck_of_admissible`);
>    - evidence table, verification record, and logs saved beside it;
>    - trust boundary: A1; the bishop reading of 3.1.2 + 3.2 + 3.5; the `Step` = FIDE-legal identification; general B0 for capture predecessors from larger material; the 5.2.2 consequence; same-session audits;
>    - "classical, no novelty".
> 5. **Ledger row.** Append `EC-T0002` to `theorems/LEDGER.csv` with Python `csv` and `lineterminator="\n"` (LF only, matching the file):
>    - `proof_commit_sha=15610256c9588e2bb5e0c19b035bbfd4437b2e31`;
>    - `lean_declaration=EndgameChess.KBK.dead_of_LKBK`;
>    - `lean_file=formal/EndgameChess/KBK.lean`;
>    - `local_proof_path=proofs/EC-C002_KBK.md`.
>
>    Then `python3 scripts/validate_ledger.py` must report `2 frozen theorem(s)`, and the unit tests must pass.
> 6. **Status.** Update `research/CANDIDATES.md` (note: frozen as EC-T0002), the `theorems/README.md` count (→ 2), `README.md`, `docs/ROADMAP.md` and `formal/README.md`.
>
> ## Closeout
> Write `sessions/S006_FREEZE_EC-T0002.md` and a `sessions/SESSION_LEDGER.md` row, recording:
> - the checks run;
> - the base SHA and proof SHA;
> - CI evidence;
> - the ledger effect (+1).
>
> Install the next prompt in full. Recommended: **S007 = EC-C003, K+N vs K is dead, Gate L only.**
> - Model knight moves directly (no blocking).
> - The material class is KNK ∪ KK; the capture branch uses EC-T0001.
> - Key lemma, analogous to B2: a king in check from a knight always has an escape. A knight attacks only squares of the opposite colour to its own, and the squares it attacks are never adjacent to one another. Find and prove the right escape-square argument; do not assume B2's argument transfers.
> - Hostile audit, independent diagnostic, mutation test. No tablebases.
>
> Then commit, push and merge to `main`.
