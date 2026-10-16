# S002 — Lean 4 formalisation of EC-C001 (Gate F)

**Date:** 2026-10-16
**Type:** Theorem session (formal verification).
**Base revision:** `2d248ee` on `main`: S001 commit `b8be692c4979680a76afe82078ea78708b9bd639` (merged to `main` in this session, plus the `AGENTS.md`/`CLAUDE.md` workflow-rule commits).
**Proof-source commit:** `342be5aefe16a9c5c882aab4f118a21472235fc3` (branch `claude/epic-goldberg-mrynfu`, merged to `main`). This closeout is in a later commit and does not cite its own SHA.

## Changes
- `formal/lean-toolchain` (`leanprover/lean4:v4.34.1`), `formal/lakefile.toml`, `formal/lake-manifest.json` (no packages): a core-only Lean project with no mathlib.
- `formal/EndgameChess/KK.lean`:
  - definitions: `Square`, `dInf`, `Adjoining`, `kingAttacks`, `Colour`, `KKState`, `inCheck`, `Admissible`, `moveKing`, `LegalKK` (rule form), `Checkmate`, `Reach` (inductive), `Dead`;
  - theorems: `attack_iff_dInf_one` (L1), `inCheck_iff` (L2′), `not_inCheck_of_admissible` (L2), `legalKK_iff_prose`, `admissible_of_legal_step` / `turn_of_legal_step` (L3), `admissible_of_last_move_legal` (L0 core), `admissible_of_reach` (L4), `not_checkmate_of_reach` (L5), **`dead_of_admissible`** (L6 / main), `dead_of_last_move_legal`, `exists_legal_move_of_admissible` (R1), `checkmate_satisfiable`, `reach_nontrivial`.
- `formal/AxiomCheck.lean`: `#print axioms` for 12 declarations.
- `audits/EC-C001_KK_LEAN.md`: fidelity audit (definition/theorem maps, 10 surrogate checks, residual gaps).
- `.github/workflows/lean-build.yml`: CI job (build, forbidden-token grep, axiom-set check).
- `formal/README.md`, `research/CANDIDATES.md`, `README.md`, `docs/ROADMAP.md`, `sessions/SESSION_LEDGER.md` updated. `NEXT_SESSION.md`: S003 installed.
- Workflow: `AGENTS.md` (canonical, for Codex and other agents) and `CLAUDE.md` (imports it). Rule: every session commits, pushes and merges to `main`.

## Findings, separated
- **Formally proved (Lean, model level):**
  - every admissible KK configuration is `Dead`;
  - every configuration produced by a `LegalKK` step is admissible, and hence dead;
  - every admissible configuration has a legal move;
  - `Checkmate` is satisfiable (in an inadmissible state), so the theorem is not vacuous.
- **Prose only (Gate L, not machine-checked):**
  - A1;
  - L3a (FIDE-legal moves = `LegalKK`);
  - general L0 for last moves that capture from larger material;
  - the 5.2.2 immediate-draw consequence.
- **Conjectured:** none new.
- **Not done:** an independent second-reader audit (both audits are same-session); a remote CI result (not observed in this session).

## Checks actually run
- Toolchain: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`, `Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)`, elan 4.2.4.
- Clean build: fresh `git clone` of the repository, checkout of `342be5aefe16a9c5c882aab4f118a21472235fc3`, no `.lake` present, `cd formal && lake build`:
```
✔ [2/4] Built EndgameChess.KK (2.8s)
✔ [3/4] Built EndgameChess (252ms)
Build completed successfully (4 jobs).
```
  Exit status 0.
- `lake env lean AxiomCheck.lean` in that clean checkout, verbatim:
```
'EndgameChess.KK.dead_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.dead_of_last_move_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.admissible_of_last_move_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.attack_iff_dInf_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.not_inCheck_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.admissible_of_legal_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.admissible_of_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.not_checkmate_of_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.legalKK_iff_prose' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.exists_legal_move_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.checkmate_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.reach_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
@EndgameChess.KK.dead_of_admissible : ∀ {p : EndgameChess.KK.KKState},
  EndgameChess.KK.Admissible p → EndgameChess.KK.Dead p
EndgameChess.KK.dead_of_last_move_legal : ∀ (q : EndgameChess.KK.KKState),
  (∃ p, EndgameChess.KK.LegalKK p q) → EndgameChess.KK.Dead q
```
- `grep -rnE '\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b' --include='*.lean' --exclude-dir=.lake formal/` → no matches (exit 1).
- `python3 -m unittest discover -s tests` → 9 tests OK. `python3 scripts/validate_ledger.py` → `LEDGER VALID: 0 frozen theorem(s) (structure only)`.
- **Not run / not observed:** GitHub Actions runs of either workflow.

## Status and ledger effect
EC-C001: `LOCAL_VERIFIED → FORMAL_VERIFIED`, recording proof commit `342be5aefe16a9c5c882aab4f118a21472235fc3`, toolchain `leanprover/lean4:v4.34.1`, declaration `EndgameChess.KK.dead_of_admissible`, and axioms `[propext, Classical.choice, Quot.sound]`. `theorems/LEDGER.csv` is unchanged (header only). Frozen theorems: **0**.

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S003: Freeze EC-C001 as EC-T0001 (Gate Z)
>
> **Owner instruction:** Execute this S003 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, and merge any unmerged session branch. EC-C001 is `FORMAL_VERIFIED` (S002). Do not treat this prompt as evidence that a freeze has happened.
>
> ## Objective
> Freeze EC-C001 as the first ledger theorem **EC-T0001**, exactly per `docs/PROOF_PROTOCOL.md` Gate Z. Cite the S002 verified proof-source commit **`342be5aefe16a9c5c882aab4f118a21472235fc3`**. Do not create a self-referential SHA. Do not change the mathematics or the Lean source.
>
> ## Required work
> 1. **Re-verify, don't trust.** In a fresh clone checked out at `342be5aefe16a9c5c882aab4f118a21472235fc3`, with toolchain `leanprover/lean4:v4.34.1` (via `elan`): run `cd formal && lake build`, `lake env lean AxiomCheck.lean`, and the word-bounded grep for `sorry|admit|axiom|unsafe|native_decide|implemented_by|extern` over `formal/**/*.lean` excluding `.lake`. Expect a successful build, `[propext, Classical.choice, Quot.sound]` for every declaration, and no grep matches. Record outputs verbatim. If anything differs, **stop**: no freeze, keep `FORMAL_VERIFIED`, install a remedial prompt.
> 2. **Drift check.** `git diff 342be5aefe16a9c5c882aab4f118a21472235fc3 HEAD -- formal/` must be empty, or contain only documentation changes, each of which you justify. If the Lean source changed, re-run Gate F on the new commit instead of freezing.
> 3. **CI evidence.** Look up the GitHub Actions results for `Lean build (EC formal proofs)` and `Ledger structural checks` on the proof commit or on `main`, using the GitHub tools. Record each run's ID, URL and conclusion if observed. Otherwise write "not observed". Never infer a pass from the workflow file.
> 4. **Manifest** `theorems/frozen/EC-T0001/v1.md`, containing:
>    - ID `EC-T0001`, source candidate EC-C001, title;
>    - exact prose statement and scope (8×8, two kings only, side to move, FIDE 2023 https://handbook.fide.com/chapter/E012023, Arts. 1.2, 1.4.1, 3.1–3.10, 5.2.2);
>    - the Lean statement copied verbatim from `#check @EndgameChess.KK.dead_of_admissible`, plus the arisen form `dead_of_last_move_legal`;
>    - local proof and audit paths;
>    - Lean file and declaration, toolchain and Lake versions, `lake-manifest.json` (no packages);
>    - the full proof-source SHA;
>    - axiom output and clean-build evidence, with the build log saved under `theorems/frozen/EC-T0001/`;
>    - verification UTC timestamp and date;
>    - **explicit trust boundary**: A1, prose L3a, general L0 (capture predecessors) and the 5.2.2 rule consequence are prose, not Lean;
>    - same-session audits noted;
>    - statement that this is a classical result with no novelty claim.
> 5. **Ledger row.** Append exactly one row to `theorems/LEDGER.csv` with `status=FROZEN`, `theorem_id=EC-T0001`, `proof_commit_sha=342be5aefe16a9c5c882aab4f118a21472235fc3`, `lean_toolchain=leanprover/lean4:v4.34.1`, `lean_declaration=EndgameChess.KK.dead_of_admissible`, `rule_edition` naming FIDE 2023, and `manifest_path`. Quote CSV fields correctly. Then run `python3 scripts/validate_ledger.py` (expect `1 frozen theorem(s)`) and `python3 -m unittest discover -s tests -v`.
> 6. **Status updates.** In `research/CANDIDATES.md`, record that EC-C001 is frozen as EC-T0001 (candidate statuses stay within the documented set; add a note and link). Update `theorems/README.md` frozen count to 1 and the README status. Optionally add an annotated git tag `EC-T0001-v1` on the freeze commit; push it only if allowed.
>
> ## Closeout
> - Write `sessions/S003_FREEZE_EC-T0001.md` and a `sessions/SESSION_LEDGER.md` row. Include: checks actually run, base SHA, proof SHA, freeze commit (described, not self-cited), CI evidence or "not observed", and the ledger effect (+1 frozen).
> - Install the next prompt in `NEXT_SESSION.md` and include it **in full** in the closeout. Recommended next prompt: **S004 = EC-C002 (K+B vs K dead position), Gate L only**. Model bishop sliding attacks with obstruction by the kings. Define a material class closed under legal moves (the lone king may capture the bishop, leaving K vs K, which connects to EC-T0001). Prove that no reachable checkmate exists for either colour. Do *not* assume checks are impossible: a bishop can give check. Mate is excluded by the geometry of escape squares, not by the absence of check. Hostile audit, diagnostic script, no tablebases.
> - Then commit, push, and merge to `main` per `AGENTS.md`.
