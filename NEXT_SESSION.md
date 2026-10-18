# NEXT SESSION — S015: Lean formalisation of EC-C007 (dead K+R vs K: forced capture / stalemate) over the rules kernel, Gate F

**Owner instruction:** Execute this S015 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C007 is `LOCAL_VERIFIED` only (S014). EC-C008 is `PROPOSED`. Do not treat this prompt as evidence that any Lean proof exists.

## Context
- Frozen: EC-T0001–EC-T0005. EC-T0003 (`Rules.dead_of_legal_into_KK`) is the dependency.
- Proof: [proofs/EC-C007_KRK_DEAD.md](proofs/EC-C007_KRK_DEAD.md) (§7 is the planned Lean statement); audit [audits/EC-C007_KRK_DEAD.md](audits/EC-C007_KRK_DEAD.md).
- **Local Lean is primary:** elan default `leanprover/lean4:v4.34.1` (commit `5045d00…`). Build and axiom-check locally from `formal/`, plus a fresh-clone build of the proof commit. Push as `jfairfaxball-348`: the repo-local git config routes github.com credentials to Git Credential Manager; use `GCM_INTERACTIVE=never`.

## Objective
Formalise EC-C007 in a **new module** `formal/EndgameChess/Rules/KRK.lean` (namespace `EndgameChess.Rules`, importing `Rules.KNK` or `Rules.Outcome`), and reach Gate F only if every Gate F check passes. **Do not freeze.** Ledger unchanged.

## Constraints
- Never edit frozen modules (`KK.lean`, `KBK.lean`, `Rules/*.lean` as frozen with EC-T0003/4/5, including `Rules/KNK.lean`). Core Lean only. No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`. No bespoke move model.

## Required work
1. `krkBoard`, `IsKRK` (as `knkBoard`/`IsKNK`, with a rook).
2. `reachK_head` (head decomposition of `ReachK`, by induction); `dead_of_succ_dead` (D1); `dead_of_succ_KK` (D2, via `dead_of_legal_into_KK`).
3. `krk_dead_of_forced_capture` (statement with `IsKRK`, `q.turn = σ.opp`, `¬MatedK q`, `∀ r, Legal q r → ∃ w b, IsKK r w b`) and `krk_forced_capture_drawn_by_rule` (with `Arisen q`).
4. **Non-vacuity by `decide`:**
   - (i) Black Ka1, White Rb2, White Kh8, Black to move: not in check; `legalMoves` is exactly `[Kxb2]`; its result is `IsKK`; the position is produced by a legal move (White Rb3–b2 from Ka1/Rb3/Kh8, White to move). Conclude `DeadK` from the main theorem.
   - (ii) Black Ka1, White Rb2, White Kc3, Black to move: stalemate (no check, `legalMoves = []`), hence `DeadK`.
   - (iii) A live contrast: a K+R vs K position with a reachable mate, e.g. a mate in one, to show the class is not uniformly dead.
   Turning "`legalMoves` is exactly this list" into `∀ r, Legal q r → …` goes through `mem_legalPositions`.
5. **Checks (local, recorded verbatim):** `lake build`; `lake env lean AxiomCheck.lean` with the new declarations added; forbidden-token grep; fresh-clone build at the proof commit; `python -m unittest discover -s tests`; `python scripts/validate_ledger.py`.
6. **Audit** `audits/EC-C007_KRK_DEAD_LEAN.md`: statement correspondence, non-vacuity, axioms, trust boundary.

## Status and next prompt
- EC-C007 → `FORMAL_VERIFIED` only if all checks pass, recording the proof commit SHA. Otherwise stay `LOCAL_VERIFIED` and state the blocker.
- If Gate F passes, install S016 = Gate Z freeze of EC-C007 as **EC-T0006**, following S013 (`sessions/S013_FREEZE_EC-T0005.md`). In S016's closeout, install S017 = **EC-C008 paper proof** (the cooperative mating route, Gate L; see the proof plan in EC-C007 §6).

## Closeout
`sessions/S015_KRK_DEAD_LEAN.md` and a `sessions/SESSION_LEDGER.md` row: changes; proved / tested / conjectured; checks actually run; base and result SHAs; status; ledger effect (none). Install the next prompt in full. Commit, push, merge to `main`.
