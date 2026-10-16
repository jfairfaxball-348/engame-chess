# S008 — Rules kernel K2: agreement with the frozen K vs K and K+B vs K models (closes G1)

**Date:** 2026-10-16
**Type:** Infrastructure/formal session. No new chess theorem; no ledger change.
**Base revision:** `4ba9a75` (`main`, S007 closeout).
**Proof-source commit:** `077572528c20bd8fa9c9e1bb06cd35f9dd4ae4bd` (branch `claude/epic-goldberg-mrynfu`, merged to `main`).

## Changes
- `formal/EndgameChess/Rules/Lemmas.lean` (new): kernel lemmas, kernel `ReachK`/`MatedK`/`DeadK`, `Chain`, and the generic `dead_transfer` theorem.
  - kernel lemmas: `attacked_iff`, `inCheck_iff`, `isPseudo_of_king`, `canCastle_false_of_noRook`, `play_kingStep`, `Position.ext'`;
  - `dead_transfer`: an exact step correspondence plus an invariant plus a mate correspondence gives dead ⇔ dead.
- `formal/EndgameChess/Rules/AgreeKK.lean` (new):
  - the `ofKK` embedding;
  - `legal_ofKK_iff`, `legalKK_iff_kernel`, `deadK_ofKK_iff`, `kernel_dead_KK`.
- `formal/EndgameChess/Rules/AgreeKBK.lean` (new):
  - `isBetween_iff_between` and `bishop_kbk`;
  - the `ofKBK`/`embPos` embeddings and the four `play_*` lemmas;
  - **`legal_ofKBK_iff`**, including the bishop capture into K vs K;
  - `deadK_embPos_iff`, `deadK_ofKBK_iff`, `kernel_dead_KBK`;
  - non-vacuity: `kernel_kk_has_move`, `kernel_kbk_check_has_move`.
- `formal/AxiomCheck.lean`: 16 K2 `#print axioms` lines and 6 `#check` lines.
- `audits/EC-C004_K2.md`: the audit.
- Status updates: `research/CANDIDATES.md` (EC-C004: K2 done, still `PROPOSED`), `docs/ROADMAP.md`, `README.md`, `formal/README.md`.
- `NEXT_SESSION.md`: S009 (K3) installed.

## Findings, separated
- **Proved (Lean):**
  - On distinct-king K vs K positions, the kernel's legal successors are exactly the embedded `KK.LegalKK` successors.
  - On `LKBK` K+B vs K positions, the kernel's legal successors are exactly the embedded `KBK.Step` successors.
  - Kernel-dead ⇔ model-dead on the frozen theorems' classes, hence `kernel_dead_KK` and `kernel_dead_KBK`.
- **Effect on the trust boundary:**
  - G1 is closed modulo the single kernel bridge `docs/RULES_KERNEL.md`. Independent human review of that bridge is still open.
  - G2 and G3 remain open (S009).
- **Correction noted:** the S006 prompt, quoted in `sessions/S005_KBK_LEAN.md`, said a knight's attacked squares are "never adjacent to one another". That is false: from a1 a knight attacks both b3 and c2, which are diagonally adjacent. The S009 prompt states the correct fact: they are never *orthogonally* adjacent, because they all have the opposite colour to the knight's square. Historical records are left unedited.

## Checks actually run
- Fresh `git clone` from GitHub, checked out at `077572528c20bd8fa9c9e1bb06cd35f9dd4ae4bd` with no `.lake`, then `cd formal && lake build`. Exit 0:
```
✔ [2/12] Built EndgameChess.KK (2.0s)
✔ [3/12] Built EndgameChess.Rules.Board (533ms)
✔ [4/12] Built EndgameChess.Rules.Position (880ms)
✔ [5/12] Built EndgameChess.Rules.Moves (822ms)
✔ [6/12] Built EndgameChess.Rules.Lemmas (1.1s)
✔ [7/12] Built EndgameChess.Rules.AgreeKK (1.1s)
✔ [8/12] Built EndgameChess.KBK (14s)
✔ [9/12] Built EndgameChess.Rules.Sanity (26s)
✔ [10/12] Built EndgameChess.Rules.AgreeKBK (15s)
✔ [11/12] Built EndgameChess (263ms)
Build completed successfully (12 jobs).
```
- `lake env lean AxiomCheck.lean`: every new declaration's axioms are a subset of `[propext, Classical.choice, Quot.sound]`; the subset gate passed.
- Forbidden-token grep: no matches.
- New module SHA-256: `Lemmas.lean` `7459ec19…0bce9152`, `AgreeKK.lean` `46a441ff…efe39d729`, `AgreeKBK.lean` `eccaa38f…2f053717`.
- Frozen and K1 modules unchanged: `KK` `4843459c…`, `KBK` `c668e0c0…`, `Board` `c21144f5…`, `Position` `8544dbf2…`, `Moves` `6a10be03…`, `Sanity` `8d161127…`.
- `python3 -m unittest discover -s tests`: OK. `python3 scripts/validate_ledger.py`: `LEDGER VALID: 2 frozen theorem(s) (structure only)`.
- **Remote CI (observed):** `Lean build (EC formal proofs)` run 38915599686 on the proof commit `0775725` itself, conclusion **success**. https://github.com/jfairfaxball-348/engame-chess/actions/runs/38915599686

## Status and ledger effect
EC-C004 stays `PROPOSED`: K1 and K2 are done, K3 is pending. `theorems/LEDGER.csv` is unchanged. Frozen theorems: **2**.

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S009: Rules kernel K3 — reachability, the 5.2.2 rule, and v2 manifests (closes G2, makes G3 explicit)
>
> **Owner instruction:** Execute this S009 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C004 is `PROPOSED` (K1 and K2 are done). Do not treat this prompt as evidence that reachability results exist.
>
> ## Context
> - **S007 (K1)** built the general kernel `formal/EndgameChess/Rules/` and the bridge `docs/RULES_KERNEL.md`.
> - **S008 (K2)** proved exact agreement (`legal_ofKK_iff`, `legal_ofKBK_iff`) and deadness transfer (`deadK_ofKK_iff`, `deadK_ofKBK_iff`, `kernel_dead_KK`, `kernel_dead_KBK`). This closed **G1**, modulo independent review of the bridge.
>
> Remaining:
> - **G2:** positions reached by a *capture from larger material*, and genuine game-reachability.
> - **G3:** the Art. 5.2.2 "immediate draw" step.
>
> ## Objective
> New modules:
> - `formal/EndgameChess/Rules/Reach.lean` (reachability and invariants);
> - `formal/EndgameChess/Rules/Outcome.lean` (the rule encoding);
> - `formal/EndgameChess/Rules/Endgames.lean` (corollaries).
>
> **Do not edit** `KK.lean`, `KBK.lean` or the K1/K2 modules (`Board`, `Position`, `Moves`, `Sanity`, `Lemmas`, `AgreeKK`, `AgreeKBK`). Record their hashes at closeout.
>
> ## Required work
> 1. **`Arisen`.** `Arisen q := ReachK initial q` (Art. 3.10.3: a position is legal iff reachable). Prove these invariants of `Arisen` positions by induction on `ReachK`:
>    - exactly one king of each colour (`countOf … = 1`);
>    - the side *not* to move is not in check (from `not_inCheck_after_legal`);
>    - a castling right implies the king and the corresponding rook are on their original squares;
>    - an en-passant target implies a pawn of the side that just moved stands in front of it, and both the target and its starting square are empty.
>
>    These are the facts needed to identify flag values on low-material positions. Prove only what step 2 needs, and state each invariant precisely.
> 2. **G2: the last move into low material.** For any kernel position `p` (any material) and `Legal p q`:
>    - if `q`'s board holds exactly two kings, then `q = ofKK a` for the corresponding `a` up to the flags (castling rights and en-passant target), and `Admissible a`;
>    - if `q` holds exactly K+B vs K, then `q = ofKBK p'` up to the flags, and `LKBK p'`.
>
>    Also prove that flags are irrelevant:
>    - with no rooks, castling rights do not affect `Legal`;
>    - with no pawns, the en-passant target does not affect `Legal` or `inCheck`;
>    - hence `DeadK` is invariant under these flags on such boards.
>
>    Combine with K2 into:
>    - **`arisen_KK_dead`**: every `Arisen` position whose material is two kings is `DeadK`;
>    - **`arisen_KBK_dead`**: the same for K+B vs K, in either orientation.
>
>    This closes **G2**.
> 3. **G3: the rule as a definition.** In `Outcome.lean`, define `GameResult := whiteWins | blackWins | draw | ongoing` and `Rules.result5_2_2`, a **named rule encoding** of Article 5.2.2 (quoted verbatim in a comment): an `Arisen` position that is `DeadK` has result `draw` immediately. Label it explicitly as a *normative encoding, not a theorem*, and add a row for it in `docs/RULES_KERNEL.md`. Derive the corollaries `kk_drawn` and `kbk_drawn`. This makes **G3** explicit.
> 4. **Checks.**
>    - `lake build`;
>    - `#print axioms` for every new main declaration (add them to `AxiomCheck.lean`);
>    - the forbidden-token grep;
>    - frozen and K1/K2 hashes unchanged;
>    - a clean-checkout build of the proof commit;
>    - CI evidence.
> 5. **Audit** `audits/EC-C004_K3.md`.
>    - Check that the invariants are not vacuous: `initial` is `Arisen`, and give a concrete `Arisen` K vs K example if feasible (a short capture sequence would be a strong non-vacuity witness, proved by `decide` if fast).
>    - Check that flag irrelevance is genuinely proved, not assumed.
> 6. **Status.** If steps 1–5 pass: EC-C004 → `LOCAL_VERIFIED` and `FORMAL_VERIFIED` (kernel claims are Lean-native; the prose bridge is the RULES_KERNEL table). Then issue **v2 manifests** `theorems/frozen/EC-T0001/v2.md` and `theorems/frozen/EC-T0002/v2.md`:
>    - each cites the S009 proof commit;
>    - each moves G1 and G2 to "closed (kernel)", and G3 to "explicit rule definition `Rules.result5_2_2`";
>    - each keeps A1 and the RULES_KERNEL human-review item.
>
>    Add superseding ledger rows, as the protocol requires, with v1 kept. **The ledger schema allows each `theorem_id` only once**, so decide and document the versioning convention first. Either extend `scripts/validate_ledger.py` with a `version` / `supersedes` column (update its tests), or use new IDs (`EC-T0001` → `EC-T0003`?). Do not silently change the schema: record the decision and the reason in `docs/PROOF_PROTOCOL.md`.
>
> ## Closeout
> Write `sessions/S009_KERNEL_K3.md` and a `sessions/SESSION_LEDGER.md` row, covering:
> - checks run, with verbatim outputs;
> - the base SHA and proof SHA;
> - hashes;
> - CI evidence;
> - candidate status;
> - the ledger effect.
>
> Install the next prompt in full: **S010 = EC-C003 (K+N vs K is dead), Gate L, stated over the kernel**:
> - model knight moves via `knightGeom`;
> - use the class K+N vs K ∪ K vs K;
> - the capture branch goes to EC-T0001 via K2;
> - prove a knight-specific key escape lemma (do not reuse B2's argument). A knight attacks only squares of the opposite colour to its own square, so no two squares it attacks are *orthogonally* adjacent, but two can be diagonally adjacent (from a1 it attacks b3 and c2). Check every such claim against the diagnostic before relying on it;
> - hostile audit, independent diagnostic, mutation test.
>
> If K3 is incomplete, install a targeted remedial S009 instead. Then commit, push and merge to `main`.
