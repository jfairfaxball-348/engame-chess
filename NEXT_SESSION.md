# NEXT SESSION — S010: Freeze the kernel-level K vs K and K+B vs K results as EC-T0003 and EC-T0004 (Gate Z)

**Owner instruction:** Execute this S010 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C005 and EC-C006 are `FORMAL_VERIFIED` (S009). Do not treat this prompt as evidence that a freeze has happened.

## Context and owner decisions
S009 (kernel K3) proved, over the general FIDE rules kernel, that every K vs K / K+B vs K position produced by *any* legal move is dead, and that every *arisen* one is too:
- `Rules.dead_of_legal_into_KK` / `_KBK`
- `Rules.arisen_KK_dead` / `_KBK_dead`

It also proved that under the explicit rule encoding `Rules.Rule5_2_2` these positions are drawn immediately (`kk_drawn_by_rule`, `kbk_drawn_by_rule`).

Owner decisions:
- these strengthened results are frozen as **new IDs**, **EC-T0003** (from EC-C005, K vs K) and **EC-T0004** (from EC-C006, K+B vs K);
- the convention is in `docs/PROOF_PROTOCOL.md`;
- the EC-T0001/EC-T0002 rows and manifests are **never rewritten**.

**Proof-source commit to cite:** `573c96a527d20f0f619a431a132a0894503c44f8`.

## Required work
1. **Re-verify only these theorems' obligation.** In a fresh GitHub clone at `573c96a527d20f0f619a431a132a0894503c44f8`, with `leanprover/lean4:v4.34.1`, run:
   - `cd formal && lake build`
   - `lake env lean AxiomCheck.lean` (the subset gate on every line)
   - the forbidden-token grep

   Also check these SHA-256 hashes:

   | Module | SHA-256 |
   |---|---|
   | `Rules/Flags.lean` | `4fcac7795bc078efb91e6bbb28bedbbad83300d57b1c5b8983937a813daa514b` |
   | `Rules/Reach.lean` | `b23a7a915bfbe8340140b1e3cc1ff3fd46f9927ffeaa920e239c6d45e4d63a94` |
   | `Rules/Outcome.lean` | `f34c14310f3e112d747622af66c47d66e48f188084dfeb7d2950797a8facedd8` |
   | `Rules/AgreeKBK.lean` | `eccaa38fa7f76095c62727f8703d9833577d4edd9357373e0dd284db2f053717` |
   | `Rules/AgreeKK.lean` | `46a441ff91c927addc2694f995d660085e11eccb822cffa8ef0aed0efe39d729` |
   | `Rules/Lemmas.lean` | `7459ec198088bd3e69ebff5f4ae767b2fccdafe49e33acac0ed5db5d0bce9152` |
   | `Rules/Moves.lean` | `6a10be0387add5e891c1e53acd567f5a9f32701082ff83c20f02c3ca3ee65958` |
   | `Rules/Position.lean` | `8544dbf23cb83798f83196366127a4afcd899da7d86689a10c23da3112447e7f` |
   | `Rules/Board.lean` | `c21144f5274cd4a4e023a7d868856a787c984cd5882e8e4e5d8ba2d015f2fdd1` |
   | `Rules/Sanity.lean` | `8d161127e5143ed06aca030fb69466f40abfa1530e935a896c68caa38254538f` |
   | `KK.lean` | `4843459ca26af93e15e5894a9f32183d46f8c554132e81051c1c21140509b1a0` |
   | `KBK.lean` | `c668e0c044cf17caa74ad8a75cfdeb0b758e3ccd5b0956ffde88cec2c895c6d7` |

   On any mismatch: stop, do not freeze, and install a remedial prompt.
2. **Drift check.** `git diff 573c96a HEAD -- formal/EndgameChess/` must be empty.
3. **CI evidence.** Use the GitHub tools to record the `Lean build (EC formal proofs)` run on `573c96a…`: its ID, URL and conclusion, or "not observed".
4. **Manifests.**
   - Write `theorems/frozen/EC-T0003/v1.md` and `theorems/frozen/EC-T0004/v1.md`, using `theorems/frozen/EC-T0001/v1.md` as the template. Save the build and axiom logs beside each.
   - Each manifest records:
     - the exact statement in prose and in Lean (verbatim `#check` of `dead_of_legal_into_KK`/`arisen_KK_dead` resp. `_KBK`, and `#print Rule5_2_2` plus the `*_drawn_by_rule` corollary);
     - the scope: FIDE 2023, the kernel modules, and the bridge `docs/RULES_KERNEL.md`, by its SHA-256 *at freeze time* (its 3.10.3 and 5.2.2 rows were added in the S009 closeout commit, after the proof commit; it is documentation, not Lean source);
     - the evidence (audits K1–K3, perft cross-checks, the S007 sanity theorems);
     - the dependency chain (EC-T0001/EC-T0002 → K2 agreement → K3).
   - **"Strengthens EC-T0001 / EC-T0002":** state how this record supersedes their trust boundary. G1 is closed by K2 agreement, G2 by K3 last-move reachability, and G3 is now the explicit named rule `Rule5_2_2`.
   - **Remaining trust boundary:**
     - A1;
     - the kernel encoding through `docs/RULES_KERNEL.md`, whose **independent human review is still open**;
     - the reading of 5.2.2 in `Rule5_2_2`;
     - the "one king per colour" `Arisen` invariant, which is not proved but not needed;
     - same-session audits;
     - the Lean kernel, toolchain and standard axioms.
   - Classical result; no novelty claim.
5. **Ledger.** Append the EC-T0003 and EC-T0004 rows using Python `csv` with `lineterminator="\n"` (LF only):
   - `proof_commit_sha=573c96a527d20f0f619a431a132a0894503c44f8`
   - `lean_declaration`: `EndgameChess.Rules.arisen_KK_dead` resp. `EndgameChess.Rules.arisen_KBK_dead`
   - `lean_file=formal/EndgameChess/Rules/Reach.lean`
   - `local_proof_path`: `audits/EC-C004_K3.md`
   - `notes`: "strengthens EC-T0001" resp. "strengthens EC-T0002"

   `python3 scripts/validate_ledger.py` must report **4** frozen theorems, and the unit tests must pass. Existing rows must stay byte-identical: check with `git diff`.
6. **Status.**
   - `research/CANDIDATES.md`: EC-C005 → frozen as EC-T0003, EC-C006 → frozen as EC-T0004.
   - `theorems/README.md`: count 4.
   - Also update `README.md`, `docs/ROADMAP.md` and `formal/README.md`.

## Closeout
- Write `sessions/S010_FREEZE_EC-T0003_T0004.md` and a `sessions/SESSION_LEDGER.md` row. Record the checks, base SHA, proof SHA, CI evidence and ledger effect (+2, giving 4).
- Install the next prompt in full, **S011 = EC-C003 (K+N vs K is dead), Gate L, stated over the kernel**:
  - Model the knight via the kernel's `knightGeom`. The class is K+N vs K ∪ K vs K, and the capture branch goes to EC-T0003.
  - Prove a knight-specific key escape lemma. Do not reuse B2's argument.
  - Correct fact to use: a knight attacks only squares of the opposite colour to its own square. So two attacked squares are never *orthogonally* adjacent, but they can be diagonally adjacent (from a1 a knight attacks b3 and c2).
  - Check every geometric claim against an independent diagnostic before relying on it.
  - Include a hostile audit and a mutation test; no tablebases.
- Then commit, push and merge to `main`.
