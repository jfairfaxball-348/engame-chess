# S009 — Rules kernel K3: flag irrelevance, last-move reachability (G2), Art. 5.2.2 rule (G3)

**Date:** 2026-10-16
**Type:** Formal session; stops at Gate F, as the owner decided. No ledger change.
**Base revision:** `90b3288` (`main`, S008 closeout).
**Proof-source commit:** `573c96a527d20f0f619a431a132a0894503c44f8` (branch `claude/epic-goldberg-mrynfu`, merged to `main`).

## Owner decisions (this session)
1. Strengthened results are frozen under **new theorem IDs**: EC-T0003 for K vs K and EC-T0004 for K+B vs K. Earlier ledger rows are never rewritten and the schema is unchanged. Recorded in `docs/PROOF_PROTOCOL.md`.
2. **Freezing happens in a separate session** (S010). K+N vs K moves to S011.

## Changes
- `formal/EndgameChess/Rules/Flags.lean` (new): castling and en-passant flags are irrelevant on boards with no rooks and no pawns (`NRP`).
  - `NRP`, `normFlags`, `nrp_pseudo`, `play_nrp`;
  - `isPseudo_normFlags`, `play_normFlags`, `isLegal_normFlags`, `nrp_of_legal`, `legal_normFlags_iff`;
  - **`deadK_normFlags_iff`**.
- `formal/EndgameChess/Rules/Reach.lean` (new): positions reached by any legal move.
  - `Arisen` (Art. 3.10.3), `IsKK`, `IsKBK`;
  - **`dead_of_legal_into_KK`**, **`dead_of_legal_into_KBK`**;
  - **`arisen_KK_dead`**, **`arisen_KBK_dead`**;
  - `initial_not_KK`, `initial_not_KBK`;
  - non-vacuity: `capture_into_KK_example` (Kxd2 takes a queen, leaving K vs K).
- `formal/EndgameChess/Rules/Outcome.lean` (new): `GameResult`; **`Rule5_2_2`**, a named normative encoding of Art. 5.2.2 (not a theorem); `kk_drawn_by_rule`, `kbk_drawn_by_rule`.
- `formal/AxiomCheck.lean`: 14 K3 `#print axioms`, plus `#check`/`#print` lines.
- `audits/EC-C004_K3.md`: the audit.
- `docs/RULES_KERNEL.md`: rows for 3.10.3 (`Arisen`) and 5.2.2 (`Rule5_2_2`). Modelling note 4 corrected: the one-king invariant is **not** proved, and is not needed.
- `docs/PROOF_PROTOCOL.md`: versioning convention.
- `research/CANDIDATES.md`:
  - EC-C004 → `FORMAL_VERIFIED`;
  - new **EC-C005** (kernel K vs K) and **EC-C006** (kernel K+B vs K), both `FORMAL_VERIFIED`;
  - EC-C003 deferred to S011.
- `docs/ROADMAP.md`, `README.md`, `formal/README.md` updated. `NEXT_SESSION.md`: S010 (freeze EC-T0003/EC-T0004) installed.

## Findings, separated
- **Proved (Lean, over the kernel):**
  - A K vs K or K+B vs K position (either orientation) produced by *any* legal move, from any material and with any flags, is dead.
  - Every arisen such position is dead.
  - Under `Rule5_2_2`, every arisen such position is drawn immediately.
- **Trust boundary now:** A1; the kernel bridge `docs/RULES_KERNEL.md`, including the reading of 5.2.2 (independent human review still open); the Lean kernel, toolchain and standard axioms; same-session audits. G1 and G2 are closed, and G3 is an explicit named rule.
- **Not proved (stated):** a general "one king per colour" invariant of `Arisen`. It is not needed.

## Checks actually run
- Fresh `git clone` from GitHub, checked out at `573c96a527d20f0f619a431a132a0894503c44f8` with no `.lake`, then `cd formal && lake build`. Exit 0:
```
✔ [2/15] Built EndgameChess.KK (2.7s)
✔ [3/15] Built EndgameChess.Rules.Board (418ms)
✔ [4/15] Built EndgameChess.Rules.Position (782ms)
✔ [5/15] Built EndgameChess.Rules.Moves (849ms)
✔ [6/15] Built EndgameChess.Rules.Lemmas (1.2s)
✔ [7/15] Built EndgameChess.Rules.AgreeKK (1.1s)
✔ [8/15] Built EndgameChess.KBK (14s)
✔ [9/15] Built EndgameChess.Rules.Sanity (26s)
✔ [10/15] Built EndgameChess.Rules.AgreeKBK (14s)
✔ [11/15] Built EndgameChess.Rules.Flags (665ms)
✔ [12/15] Built EndgameChess.Rules.Reach (630ms)
✔ [13/15] Built EndgameChess.Rules.Outcome (308ms)
✔ [14/15] Built EndgameChess (248ms)
Build completed successfully (15 jobs).
```
- `lake env lean AxiomCheck.lean`: every line passes the subset gate. All K3 declarations are within `[propext, Classical.choice, Quot.sound]`; `isPseudo_normFlags`, `initial_not_KK` and `initial_not_KBK` use only `[propext]`.
- Forbidden-token grep: no matches.
- New module SHA-256:
  - `Flags.lean` `4fcac7795bc078efb91e6bbb28bedbbad83300d57b1c5b8983937a813daa514b`
  - `Reach.lean` `b23a7a915bfbe8340140b1e3cc1ff3fd46f9927ffeaa920e239c6d45e4d63a94`
  - `Outcome.lean` `f34c14310f3e112d747622af66c47d66e48f188084dfeb7d2950797a8facedd8`
- Frozen, K1 and K2 modules unchanged (hashes listed in `NEXT_SESSION.md`).
- `python3 -m unittest discover -s tests`: OK. `python3 scripts/validate_ledger.py`: `LEDGER VALID: 2 frozen theorem(s) (structure only)`.
- **Remote CI (observed):** `Lean build (EC formal proofs)` run 38918432537 on the proof commit `573c96a` itself, conclusion **success**. https://github.com/jfairfaxball-348/engame-chess/actions/runs/38918432537

## Status and ledger effect
EC-C004, EC-C005 and EC-C006 are `FORMAL_VERIFIED`. `theorems/LEDGER.csv` is unchanged. Frozen theorems: **2**.

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S010: Freeze the kernel-level K vs K and K+B vs K results as EC-T0003 and EC-T0004 (Gate Z)
>
> **Owner instruction:** Execute this S010 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C005 and EC-C006 are `FORMAL_VERIFIED` (S009). Do not treat this prompt as evidence that a freeze has happened.
>
> ## Context and owner decisions
> S009 (kernel K3) proved, over the general FIDE rules kernel, that every K vs K / K+B vs K position produced by *any* legal move is dead, and that every *arisen* one is too:
> - `Rules.dead_of_legal_into_KK` / `_KBK`
> - `Rules.arisen_KK_dead` / `_KBK_dead`
>
> It also proved that under the explicit rule encoding `Rules.Rule5_2_2` these positions are drawn immediately (`kk_drawn_by_rule`, `kbk_drawn_by_rule`).
>
> Owner decisions:
> - these strengthened results are frozen as **new IDs**, **EC-T0003** (from EC-C005, K vs K) and **EC-T0004** (from EC-C006, K+B vs K);
> - the convention is in `docs/PROOF_PROTOCOL.md`;
> - the EC-T0001/EC-T0002 rows and manifests are **never rewritten**.
>
> **Proof-source commit to cite:** `573c96a527d20f0f619a431a132a0894503c44f8`.
>
> ## Required work
> 1. **Re-verify only these theorems' obligation.** In a fresh GitHub clone at `573c96a527d20f0f619a431a132a0894503c44f8`, with `leanprover/lean4:v4.34.1`, run:
>    - `cd formal && lake build`
>    - `lake env lean AxiomCheck.lean` (the subset gate on every line)
>    - the forbidden-token grep
>
>    Also check these SHA-256 hashes:
>
>    | Module | SHA-256 |
>    |---|---|
>    | `Rules/Flags.lean` | `4fcac7795bc078efb91e6bbb28bedbbad83300d57b1c5b8983937a813daa514b` |
>    | `Rules/Reach.lean` | `b23a7a915bfbe8340140b1e3cc1ff3fd46f9927ffeaa920e239c6d45e4d63a94` |
>    | `Rules/Outcome.lean` | `f34c14310f3e112d747622af66c47d66e48f188084dfeb7d2950797a8facedd8` |
>    | `Rules/AgreeKBK.lean` | `eccaa38fa7f76095c62727f8703d9833577d4edd9357373e0dd284db2f053717` |
>    | `Rules/AgreeKK.lean` | `46a441ff91c927addc2694f995d660085e11eccb822cffa8ef0aed0efe39d729` |
>    | `Rules/Lemmas.lean` | `7459ec198088bd3e69ebff5f4ae767b2fccdafe49e33acac0ed5db5d0bce9152` |
>    | `Rules/Moves.lean` | `6a10be0387add5e891c1e53acd567f5a9f32701082ff83c20f02c3ca3ee65958` |
>    | `Rules/Position.lean` | `8544dbf23cb83798f83196366127a4afcd899da7d86689a10c23da3112447e7f` |
>    | `Rules/Board.lean` | `c21144f5274cd4a4e023a7d868856a787c984cd5882e8e4e5d8ba2d015f2fdd1` |
>    | `Rules/Sanity.lean` | `8d161127e5143ed06aca030fb69466f40abfa1530e935a896c68caa38254538f` |
>    | `KK.lean` | `4843459ca26af93e15e5894a9f32183d46f8c554132e81051c1c21140509b1a0` |
>    | `KBK.lean` | `c668e0c044cf17caa74ad8a75cfdeb0b758e3ccd5b0956ffde88cec2c895c6d7` |
>
>    On any mismatch: stop, do not freeze, and install a remedial prompt.
> 2. **Drift check.** `git diff 573c96a HEAD -- formal/EndgameChess/` must be empty.
> 3. **CI evidence.** Use the GitHub tools to record the `Lean build (EC formal proofs)` run on `573c96a…`: its ID, URL and conclusion, or "not observed".
> 4. **Manifests.**
>    - Write `theorems/frozen/EC-T0003/v1.md` and `theorems/frozen/EC-T0004/v1.md`, using `theorems/frozen/EC-T0001/v1.md` as the template. Save the build and axiom logs beside each.
>    - Each manifest records:
>      - the exact statement in prose and in Lean (verbatim `#check` of `dead_of_legal_into_KK`/`arisen_KK_dead` resp. `_KBK`, and `#print Rule5_2_2` plus the `*_drawn_by_rule` corollary);
>      - the scope: FIDE 2023, the kernel modules, and the bridge `docs/RULES_KERNEL.md`, by its SHA-256 *at freeze time* (its 3.10.3 and 5.2.2 rows were added in the S009 closeout commit, after the proof commit; it is documentation, not Lean source);
>      - the evidence (audits K1–K3, perft cross-checks, the S007 sanity theorems);
>      - the dependency chain (EC-T0001/EC-T0002 → K2 agreement → K3).
>    - **"Strengthens EC-T0001 / EC-T0002":** state how this record supersedes their trust boundary. G1 is closed by K2 agreement, G2 by K3 last-move reachability, and G3 is now the explicit named rule `Rule5_2_2`.
>    - **Remaining trust boundary:**
>      - A1;
>      - the kernel encoding through `docs/RULES_KERNEL.md`, whose **independent human review is still open**;
>      - the reading of 5.2.2 in `Rule5_2_2`;
>      - the "one king per colour" `Arisen` invariant, which is not proved but not needed;
>      - same-session audits;
>      - the Lean kernel, toolchain and standard axioms.
>    - Classical result; no novelty claim.
> 5. **Ledger.** Append the EC-T0003 and EC-T0004 rows using Python `csv` with `lineterminator="\n"` (LF only):
>    - `proof_commit_sha=573c96a527d20f0f619a431a132a0894503c44f8`
>    - `lean_declaration`: `EndgameChess.Rules.arisen_KK_dead` resp. `EndgameChess.Rules.arisen_KBK_dead`
>    - `lean_file=formal/EndgameChess/Rules/Reach.lean`
>    - `local_proof_path`: `audits/EC-C004_K3.md`
>    - `notes`: "strengthens EC-T0001" resp. "strengthens EC-T0002"
>
>    `python3 scripts/validate_ledger.py` must report **4** frozen theorems, and the unit tests must pass. Existing rows must stay byte-identical: check with `git diff`.
> 6. **Status.**
>    - `research/CANDIDATES.md`: EC-C005 → frozen as EC-T0003, EC-C006 → frozen as EC-T0004.
>    - `theorems/README.md`: count 4.
>    - Also update `README.md`, `docs/ROADMAP.md` and `formal/README.md`.
>
> ## Closeout
> - Write `sessions/S010_FREEZE_EC-T0003_T0004.md` and a `sessions/SESSION_LEDGER.md` row. Record the checks, base SHA, proof SHA, CI evidence and ledger effect (+2, giving 4).
> - Install the next prompt in full, **S011 = EC-C003 (K+N vs K is dead), Gate L, stated over the kernel**:
>   - Model the knight via the kernel's `knightGeom`. The class is K+N vs K ∪ K vs K, and the capture branch goes to EC-T0003.
>   - Prove a knight-specific key escape lemma. Do not reuse B2's argument.
>   - Correct fact to use: a knight attacks only squares of the opposite colour to its own square. So two attacked squares are never *orthogonally* adjacent, but they can be diagonally adjacent (from a1 a knight attacks b3 and c2).
>   - Check every geometric claim against an independent diagnostic before relying on it.
>   - Include a hostile audit and a mutation test; no tablebases.
> - Then commit, push and merge to `main`.
