# NEXT SESSION — S006: Freeze EC-C002 as EC-T0002 (Gate Z)

**Owner instruction:** Execute this S006 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C002 is `FORMAL_VERIFIED` (S005). Do not treat this prompt as evidence that a freeze has happened.

## Objective
Freeze EC-C002 as **EC-T0002** per `docs/PROOF_PROTOCOL.md` Gate Z, citing the S005 proof-source commit **`15610256c9588e2bb5e0c19b035bbfd4437b2e31`**. Use `theorems/frozen/EC-T0001/v1.md` as the template. Do not change the mathematics or `formal/EndgameChess/KBK.lean` / `KK.lean`.

## Required work
1. **Re-verify (only this theorem's obligation).** In a fresh clone at `15610256c9588e2bb5e0c19b035bbfd4437b2e31`, with `leanprover/lean4:v4.34.1`, run:
   - `cd formal && lake build`;
   - `lake env lean AxiomCheck.lean` (every `EndgameChess.KBK.*` report must be a subset of `[propext, Classical.choice, Quot.sound]` or "does not depend on any axioms");
   - the forbidden-token grep.

   Record each SHA-256: `KBK.lean` must be `c668e0c044cf17caa74ad8a75cfdeb0b758e3ccd5b0956ffde88cec2c895c6d7`, and `KK.lean` must still be `4843459ca26af93e15e5894a9f32183d46f8c554132e81051c1c21140509b1a0`. On any mismatch, stop: no freeze, and install a remedial prompt.
2. **Drift check.** `git diff 15610256 HEAD -- formal/EndgameChess/` must be empty. Documentation-only changes elsewhere in `formal/` are fine; justify each one.
3. **CI evidence.** Use the GitHub tools to look up the `Lean build (EC formal proofs)` run on the proof commit or on `main`, with an identical `formal/EndgameChess/`. Record its ID, URL and conclusion, or write "not observed".
4. **Manifest** `theorems/frozen/EC-T0002/v1.md`, with the same sections as EC-T0001:
   - statement and scope (both orientations; FIDE 2023 Arts 1.2, 1.4.1, 3.1–3.2, 3.5, 3.8–3.10, 5.2.2);
   - the verbatim `#check` output of `dead_of_LKBK` and `dead_of_step`;
   - the dependency on EC-T0001 (lemmas used: `admissible_of_legal_step`, `not_inCheck_of_admissible`);
   - evidence table, verification record, and logs saved beside it;
   - trust boundary: A1; the bishop reading of 3.1.2 + 3.2 + 3.5; the `Step` = FIDE-legal identification; general B0 for capture predecessors from larger material; the 5.2.2 consequence; same-session audits;
   - "classical, no novelty".
5. **Ledger row.** Append `EC-T0002` to `theorems/LEDGER.csv` with Python `csv` and `lineterminator="\n"` (LF only, matching the file):
   - `proof_commit_sha=15610256c9588e2bb5e0c19b035bbfd4437b2e31`;
   - `lean_declaration=EndgameChess.KBK.dead_of_LKBK`;
   - `lean_file=formal/EndgameChess/KBK.lean`;
   - `local_proof_path=proofs/EC-C002_KBK.md`.

   Then `python3 scripts/validate_ledger.py` must report `2 frozen theorem(s)`, and the unit tests must pass.
6. **Status.** Update `research/CANDIDATES.md` (note: frozen as EC-T0002), the `theorems/README.md` count (→ 2), `README.md`, `docs/ROADMAP.md` and `formal/README.md`.

## Closeout
Write `sessions/S006_FREEZE_EC-T0002.md` and a `sessions/SESSION_LEDGER.md` row, recording:
- the checks run;
- the base SHA and proof SHA;
- CI evidence;
- the ledger effect (+1).

Install the next prompt in full. Recommended: **S007 = EC-C003, K+N vs K is dead, Gate L only.**
- Model knight moves directly (no blocking).
- The material class is KNK ∪ KK; the capture branch uses EC-T0001.
- Key lemma, analogous to B2: a king in check from a knight always has an escape. A knight attacks only squares of the opposite colour to its own, and the squares it attacks are never adjacent to one another. Find and prove the right escape-square argument; do not assume B2's argument transfers.
- Hostile audit, independent diagnostic, mutation test. No tablebases.

Then commit, push and merge to `main`.
