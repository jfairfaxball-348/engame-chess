# NEXT SESSION — S009: Rules kernel K3 — reachability, the 5.2.2 rule, and v2 manifests (closes G2, makes G3 explicit)

**Owner instruction:** Execute this S009 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C004 is `PROPOSED` (K1 and K2 are done). Do not treat this prompt as evidence that reachability results exist.

## Context
- **S007 (K1)** built the general kernel `formal/EndgameChess/Rules/` and the bridge `docs/RULES_KERNEL.md`.
- **S008 (K2)** proved exact agreement (`legal_ofKK_iff`, `legal_ofKBK_iff`) and deadness transfer (`deadK_ofKK_iff`, `deadK_ofKBK_iff`, `kernel_dead_KK`, `kernel_dead_KBK`). This closed **G1**, modulo independent review of the bridge.

Remaining:
- **G2:** positions reached by a *capture from larger material*, and genuine game-reachability.
- **G3:** the Art. 5.2.2 "immediate draw" step.

## Objective
New modules:
- `formal/EndgameChess/Rules/Reach.lean` (reachability and invariants);
- `formal/EndgameChess/Rules/Outcome.lean` (the rule encoding);
- `formal/EndgameChess/Rules/Endgames.lean` (corollaries).

**Do not edit** `KK.lean`, `KBK.lean` or the K1/K2 modules (`Board`, `Position`, `Moves`, `Sanity`, `Lemmas`, `AgreeKK`, `AgreeKBK`). Record their hashes at closeout.

## Required work
1. **`Arisen`.** `Arisen q := ReachK initial q` (Art. 3.10.3: a position is legal iff reachable). Prove these invariants of `Arisen` positions by induction on `ReachK`:
   - exactly one king of each colour (`countOf … = 1`);
   - the side *not* to move is not in check (from `not_inCheck_after_legal`);
   - a castling right implies the king and the corresponding rook are on their original squares;
   - an en-passant target implies a pawn of the side that just moved stands in front of it, and both the target and its starting square are empty.

   These are the facts needed to identify flag values on low-material positions. Prove only what step 2 needs, and state each invariant precisely.
2. **G2: the last move into low material.** For any kernel position `p` (any material) and `Legal p q`:
   - if `q`'s board holds exactly two kings, then `q = ofKK a` for the corresponding `a` up to the flags (castling rights and en-passant target), and `Admissible a`;
   - if `q` holds exactly K+B vs K, then `q = ofKBK p'` up to the flags, and `LKBK p'`.

   Also prove that flags are irrelevant:
   - with no rooks, castling rights do not affect `Legal`;
   - with no pawns, the en-passant target does not affect `Legal` or `inCheck`;
   - hence `DeadK` is invariant under these flags on such boards.

   Combine with K2 into:
   - **`arisen_KK_dead`**: every `Arisen` position whose material is two kings is `DeadK`;
   - **`arisen_KBK_dead`**: the same for K+B vs K, in either orientation.

   This closes **G2**.
3. **G3: the rule as a definition.** In `Outcome.lean`, define `GameResult := whiteWins | blackWins | draw | ongoing` and `Rules.result5_2_2`, a **named rule encoding** of Article 5.2.2 (quoted verbatim in a comment): an `Arisen` position that is `DeadK` has result `draw` immediately. Label it explicitly as a *normative encoding, not a theorem*, and add a row for it in `docs/RULES_KERNEL.md`. Derive the corollaries `kk_drawn` and `kbk_drawn`. This makes **G3** explicit.
4. **Checks.**
   - `lake build`;
   - `#print axioms` for every new main declaration (add them to `AxiomCheck.lean`);
   - the forbidden-token grep;
   - frozen and K1/K2 hashes unchanged;
   - a clean-checkout build of the proof commit;
   - CI evidence.
5. **Audit** `audits/EC-C004_K3.md`.
   - Check that the invariants are not vacuous: `initial` is `Arisen`, and give a concrete `Arisen` K vs K example if feasible (a short capture sequence would be a strong non-vacuity witness, proved by `decide` if fast).
   - Check that flag irrelevance is genuinely proved, not assumed.
6. **Status.** If steps 1–5 pass: EC-C004 → `LOCAL_VERIFIED` and `FORMAL_VERIFIED` (kernel claims are Lean-native; the prose bridge is the RULES_KERNEL table). Then issue **v2 manifests** `theorems/frozen/EC-T0001/v2.md` and `theorems/frozen/EC-T0002/v2.md`:
   - each cites the S009 proof commit;
   - each moves G1 and G2 to "closed (kernel)", and G3 to "explicit rule definition `Rules.result5_2_2`";
   - each keeps A1 and the RULES_KERNEL human-review item.

   Add superseding ledger rows, as the protocol requires, with v1 kept. **The ledger schema allows each `theorem_id` only once**, so decide and document the versioning convention first. Either extend `scripts/validate_ledger.py` with a `version` / `supersedes` column (update its tests), or use new IDs (`EC-T0001` → `EC-T0003`?). Do not silently change the schema: record the decision and the reason in `docs/PROOF_PROTOCOL.md`.

## Closeout
Write `sessions/S009_KERNEL_K3.md` and a `sessions/SESSION_LEDGER.md` row, covering:
- checks run, with verbatim outputs;
- the base SHA and proof SHA;
- hashes;
- CI evidence;
- candidate status;
- the ledger effect.

Install the next prompt in full: **S010 = EC-C003 (K+N vs K is dead), Gate L, stated over the kernel**:
- model knight moves via `knightGeom`;
- use the class K+N vs K ∪ K vs K;
- the capture branch goes to EC-T0001 via K2;
- prove a knight-specific key escape lemma (do not reuse B2's argument). A knight attacks only squares of the opposite colour to its own square, so no two squares it attacks are *orthogonally* adjacent, but two can be diagonally adjacent (from a1 it attacks b3 and c2). Check every such claim against the diagnostic before relying on it;
- hostile audit, independent diagnostic, mutation test.

If K3 is incomplete, install a targeted remedial S009 instead. Then commit, push and merge to `main`.
