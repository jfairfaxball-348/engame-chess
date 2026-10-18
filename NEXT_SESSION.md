# NEXT SESSION — S022: Lean formalisation of EC-C008, second part, then Gate F

**Owner instruction:** Execute this S022 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C008 is `LOCAL_VERIFIED` (S019). Lean part 1 is done (S021). Do not treat this prompt as evidence that any further Lean proof exists.

## Overarching objective (owner, 2026-10-18)
**Proof-based tablebase equivalence:** for every ending with fewer than 8 pieces, prove the outcome as a closed mathematical characterisation in Lean, **never by lookup or per-position enumeration** (`docs/CHARTER.md`, `docs/ROADMAP.md`). Together with EC-T0006, EC-C008 settles layer L1 (dead/live) for K+R vs K.

## Context
- Proof: [proofs/EC-C008_KRK_LIVE.md](proofs/EC-C008_KRK_LIVE.md) §1, §2, §3 (P1) and §4b. Audits: [audits/EC-C008_KRK_LIVE.md](audits/EC-C008_KRK_LIVE.md) (prose) and [audits/EC-C008_KRK_LIVE_LEAN.md](audits/EC-C008_KRK_LIVE_LEAN.md) (Lean part 1, including §6, notes for S022).
- **Already formalised (S021, do not edit unless a fix is needed — they are not frozen):**
  - `Rules/KRKLive/Basic.lean`:
    - `attacked_krk` and `inCheck_*_krk`;
    - the move model `StepM`/`MateM`/`WinM`, with kernel soundness `step_sound`, `mate_sound` and `not_deadK_of_winM` (any flags);
    - F4 via `BoardSym`, `winM_of_sym` and `exists_sym_normal`.
  - `Rules/KRKLive/Endgame.lean`:
    - Lemmas M, E, C, W and S (`krk_lemmaM` … `krk_lemmaS`);
    - the kernel form `krk_settled_live`: rook on h8, strong side to move, `Normal sk`, lone king not in check ⇒ `¬DeadK`.
- **Toolchain:** `leanprover/lean4:v4.35.0`. Run `lake build` and `lake env lean AxiomCheck.lean` locally from `formal/`.
- The Palomar module-system port is not done. Do not start it unasked.
- No `native_decide`, no custom axioms, no per-position certificates. Small `decide` checks are fine for concrete non-vacuity witnesses and for bounded local lemmas.

## Constraints
- Never edit frozen modules: `KK`, `KBK`, and the `Rules/*` modules frozen with EC-T0003–T0006, including `KNK.lean` and `KRK.lean`.
- New work goes in new modules, e.g. `Rules/KRKLive/Relocation.lean` (RL-h, RL-f, P1) and `Rules/KRKLive/Main.lean` (main theorem), with one module per main theorem.
- Core Lean only. No `sorry`, `admit`, custom `axiom` or `unsafe`.

## Required work
1. **RL-h and RL-f**, stated in the model as schemas:
   - the lone king to move has a `StepM.lone` successor, or the state is `MateM`;
   - state the exception `(c8, h7, a8)` of RL-h explicitly.
2. **P1** (relocation): from every normalised state, with the strong side to move, the lone king not seen by the rook and the kings apart, `WinM` holds. The route is P1 into `krk_lemmaS`. The lone king may play *any* reply satisfying `StepM.lone`, so prove each leg for all such replies. Branches: home, direct, HV, FS (F1/F2/F3).
3. **Main theorem** `krk_strong_to_move_live` (EC-C008(a)): `Legal p q`, `IsKRK q σ sk rs wk`, `q.turn = σ` ⇒ `¬DeadK q`.
   - F1: from legality of the last move, the lone king is not in check and the kings are apart.
   - Normalise with `exists_sym_normal`, then transfer with `winM_of_sym` and `not_deadK_of_winM`.
4. **`krk_dead_iff`** (EC-C008(b)): with the lone king to move, `DeadK q ↔ ¬MatedK q ∧ ∀ r, Legal q r → ∃ w b, IsKK r w b`. Use EC-T0006 for "⇐", and (a) for "⇒".
   - The "⇒" direction needs: a non-capturing lone-king move from a K+R vs K position gives K+R vs K with the strong side to move, produced by a legal move.
   - Also: every legal lone-king move either captures the rook (giving `IsKK`) or not.
5. Arisen and `Rule5_2_2` corollaries, as for EC-T0005/T0006.
6. **Non-vacuity** by `decide`. This includes the RL-h stalemate exception: White Kc8, Rh7, Black Ka8, Black to move, `legalMoves = []`, not in check.
7. **Checks**, run locally and recorded verbatim: `lake build`; `AxiomCheck` with the new declarations; the forbidden-token grep; the Python tests (`python3 -m unittest discover -s tests`); the ledger validation.
8. **Lean audit:** complete `audits/EC-C008_KRK_LIVE_LEAN.md`. If the main theorem is proved and all checks pass, EC-C008 becomes `FORMAL_VERIFIED` (Gate F). Do not freeze in the same session (Gate Z is S023).

## Closeout
- Write `sessions/S022_KRK_LIVE_LEAN2.md` and a `sessions/SESSION_LEDGER.md` row covering: changes; checks actually run; SHAs; status; ledger effect (none).
- Install S023: Gate Z freeze of EC-C008 (as EC-T0007) if Gate F passed; otherwise the remaining formalisation.
- Commit, push, merge to `main`.
