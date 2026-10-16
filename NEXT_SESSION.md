# NEXT SESSION — S003: Freeze EC-C001 as EC-T0001 (Gate Z)

**Owner instruction:** Execute this S003 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, and merge any unmerged session branch. EC-C001 is `FORMAL_VERIFIED` (S002). Do not treat this prompt as evidence that a freeze has happened.

## Objective
Freeze EC-C001 as the first ledger theorem **EC-T0001**, exactly per `docs/PROOF_PROTOCOL.md` Gate Z. Cite the S002 verified proof-source commit **`342be5aefe16a9c5c882aab4f118a21472235fc3`**. Do not create a self-referential SHA. Do not change the mathematics or the Lean source.

## Required work
1. **Re-verify, don't trust.** In a fresh clone checked out at `342be5aefe16a9c5c882aab4f118a21472235fc3`, with toolchain `leanprover/lean4:v4.34.1` (via `elan`): run `cd formal && lake build`, `lake env lean AxiomCheck.lean`, and the word-bounded grep for `sorry|admit|axiom|unsafe|native_decide|implemented_by|extern` over `formal/**/*.lean` excluding `.lake`. Expect a successful build, `[propext, Classical.choice, Quot.sound]` for every declaration, and no grep matches. Record outputs verbatim. If anything differs, **stop**: no freeze, keep `FORMAL_VERIFIED`, install a remedial prompt.
2. **Drift check.** `git diff 342be5aefe16a9c5c882aab4f118a21472235fc3 HEAD -- formal/` must be empty, or contain only documentation changes, each of which you justify. If the Lean source changed, re-run Gate F on the new commit instead of freezing.
3. **CI evidence.** Look up the GitHub Actions results for `Lean build (EC formal proofs)` and `Ledger structural checks` on the proof commit or on `main`, using the GitHub tools. Record each run's ID, URL and conclusion if observed. Otherwise write "not observed". Never infer a pass from the workflow file.
4. **Manifest** `theorems/frozen/EC-T0001/v1.md`, containing:
   - ID `EC-T0001`, source candidate EC-C001, title;
   - exact prose statement and scope (8×8, two kings only, side to move, FIDE 2023 https://handbook.fide.com/chapter/E012023, Arts. 1.2, 1.4.1, 3.1–3.10, 5.2.2);
   - the Lean statement copied verbatim from `#check @EndgameChess.KK.dead_of_admissible`, plus the arisen form `dead_of_last_move_legal`;
   - local proof and audit paths;
   - Lean file and declaration, toolchain and Lake versions, `lake-manifest.json` (no packages);
   - the full proof-source SHA;
   - axiom output and clean-build evidence, with the build log saved under `theorems/frozen/EC-T0001/`;
   - verification UTC timestamp and date;
   - **explicit trust boundary**: A1, prose L3a, general L0 (capture predecessors) and the 5.2.2 rule consequence are prose, not Lean;
   - same-session audits noted;
   - statement that this is a classical result with no novelty claim.
5. **Ledger row.** Append exactly one row to `theorems/LEDGER.csv` with `status=FROZEN`, `theorem_id=EC-T0001`, `proof_commit_sha=342be5aefe16a9c5c882aab4f118a21472235fc3`, `lean_toolchain=leanprover/lean4:v4.34.1`, `lean_declaration=EndgameChess.KK.dead_of_admissible`, `rule_edition` naming FIDE 2023, and `manifest_path`. Quote CSV fields correctly. Then run `python3 scripts/validate_ledger.py` (expect `1 frozen theorem(s)`) and `python3 -m unittest discover -s tests -v`.
6. **Status updates.** In `research/CANDIDATES.md`, record that EC-C001 is frozen as EC-T0001 (candidate statuses stay within the documented set; add a note and link). Update `theorems/README.md` frozen count to 1 and the README status. Optionally add an annotated git tag `EC-T0001-v1` on the freeze commit; push it only if allowed.

## Closeout
- Write `sessions/S003_FREEZE_EC-T0001.md` and a `sessions/SESSION_LEDGER.md` row. Include: checks actually run, base SHA, proof SHA, freeze commit (described, not self-cited), CI evidence or "not observed", and the ledger effect (+1 frozen).
- Install the next prompt in `NEXT_SESSION.md` and include it **in full** in the closeout. Recommended next prompt: **S004 = EC-C002 (K+B vs K dead position), Gate L only**. Model bishop sliding attacks with obstruction by the kings. Define a material class closed under legal moves (the lone king may capture the bishop, leaving K vs K, which connects to EC-T0001). Prove that no reachable checkmate exists for either colour. Do *not* assume checks are impossible: a bishop can give check. Mate is excluded by the geometry of escape squares, not by the absence of check. Hostile audit, diagnostic script, no tablebases.
- Then commit, push, and merge to `main` per `AGENTS.md`.
