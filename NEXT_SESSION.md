# NEXT SESSION — S012: Lean formalisation of EC-C003 (K+N vs K dead) over the rules kernel, Gate F

**Owner instruction:** Execute this S012 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C003 is `LOCAL_VERIFIED` only (S011). Do not treat this prompt as evidence that any Lean proof exists.

## Context
- Frozen: EC-T0001 (K vs K, bespoke), EC-T0002 (K+B vs K, bespoke), EC-T0003 (K vs K over the kernel), EC-T0004 (K+B vs K over the kernel).
- S011 proved on paper ([proofs/EC-C003_KNK.md](proofs/EC-C003_KNK.md), audit [audits/EC-C003_KNK.md](audits/EC-C003_KNK.md)) that every K+N vs K position produced by a legal move is dead under the kernel. Note proof §0: a checking knight attacks only squares of the checked king's **colour**, so it never attacks an orthogonal neighbour (the S011 prompt had this reversed).
- **Local Lean is the primary check.** elan is installed on the owner's machine with default toolchain `leanprover/lean4:v4.34.1` (commit `5045d00…`), the version pinned in `formal/lean-toolchain` and recorded in the frozen manifests. Run `lake build` and the axiom check locally from `formal/` and record the observed output. CI is secondary; never claim a CI result that was not observed.

## Objective
Formalise the S011 proof in a **new module** `formal/EndgameChess/Rules/KNK.lean` (namespace `EndgameChess.Rules`), directly over the kernel, and reach Gate F (`FORMAL_VERIFIED`) only if every Gate F check in `docs/PROOF_PROTOCOL.md` passes. **Do not freeze** (that is S013). `theorems/LEDGER.csv` stays unchanged.

## Constraints
- **Never edit frozen modules**: `KK.lean`, `KBK.lean`, and the kernel modules underlying EC-T0003/0004 (`Rules/*.lean` as of `573c96a`). Import them. If a shared helper is missing, put it in `Rules/KNK.lean` (or a new shared module, then check that every frozen downstream module still builds with the same statements and axioms).
- Core Lean only; toolchain unchanged. No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`.
- No bespoke move model: state and prove everything over `Rules.Legal`, `ReachK`, `MatedK`, `DeadK`.
- Verify only what is an obligation: the new module and its importers (`EndgameChess.lean`, `AxiomCheck.lean`).

## Required work
1. **Definitions:** `knkBoard σ sk ns wk` (σ king on `sk`, σ knight on `ns`, σ.opp king on `wk`, else empty) and `IsKNK q σ sk ns wk := sk ≠ ns ∧ sk ≠ wk ∧ ns ≠ wk ∧ q.board = knkBoard σ sk ns wk`.
2. **Lemmas mirroring the proof:**
   - `nrp_knkBoard` (no rooks/pawns);
   - `attacked`/`inCheck` characterisation on a `knkBoard` (knight and king attacks are board-independent);
   - N0: `kings_apart_of_legal_into_KNK`, `strong_not_inCheck_KNK`;
   - N1: `knightGeom` colour flip; `not_knightGeom_orth_of_knightGeom` (N1(c)); `dInf_eq_two_of_knightGeom` (N1(b));
   - **N2: `weak_has_move_KNK`** by the `h`/`v` construction (not enumeration);
   - N3: closure of `C r := (∃ p, Legal p r) ∧ (KNK board ∨ KK board)` under `Legal` (σ moves keep material; ω king may capture the knight → `IsKK`);
   - N4: induction on `ReachK`; the K vs K branch closed by the frozen `dead_of_legal_into_KK`;
   - `initial_not_KNK`.
3. **Main theorems:** `dead_of_legal_into_KNK`, `arisen_KNK_dead`, `knk_drawn_by_rule` (the last uses `Rule5_2_2`; import `Rules.Outcome`).
4. **Non-vacuity (by `decide` on concrete positions where feasible):** a legal K+N vs K position in which the knight gives check; a K+N vs K stalemate (e.g. Black Ka8, White Kb6 + Nc6, Black to move); a capture of the knight into K vs K.
5. **Checks (run locally, record verbatim):** `lake build` (new module + `EndgameChess`), `lake env lean AxiomCheck.lean` with the new declarations added (expect ⊆ `[propext, Classical.choice, Quot.sound]`), a grep for forbidden tokens, `python -m unittest discover -s tests`, `python scripts/validate_ledger.py`.
6. **Audit:** `audits/EC-C003_KNK_LEAN.md` — statement-to-prose correspondence (both orientations, any predecessor, any flags), no vacuity, axioms, trust boundary (A1, kernel bridge review still open).

## Status
- EC-C003 → `FORMAL_VERIFIED` only if all checks pass, recording the proof-source commit SHA; otherwise stay `LOCAL_VERIFIED` and state the blocker.
- If Gate F passes, install S013 = Gate Z freeze of EC-C003 as **EC-T0005** (fresh-clone local verification of the proof commit, manifest `theorems/frozen/EC-T0005/v1.md`, one ledger row). Otherwise a remedial S012.

## Closeout
`sessions/S012_KNK_LEAN.md` and a `sessions/SESSION_LEDGER.md` row: changes; proved / tested / conjectured lists; checks actually run (local and CI separately); base and result SHAs; candidate status; ledger effect (none). Install the next prompt in full. Commit, push, merge to `main`.
