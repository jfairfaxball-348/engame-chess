# S022 — EC-C008 Lean formalisation, part 2 (replies, relocation, main theorems; Gate F)

**Date:** 2026-10-18
**Type:** Formalisation session (Gate F). No freeze.
**Base revision:** `86d36b9` (`main` after S021).
**Lean proof-source commit:** `a8bc161d2a51b92c340697af16a10e874cd9a098`. The closeout commit follows it.

## Changes
- `formal/EndgameChess/Rules/KRKLive/Reply.lean` (new):
  - `Free`, `LoneOK` and `HExc`;
  - **Lemma RL-h** (`krk_RLh`) and **Lemma RL-f** (`krk_RLf`), proved by explicit reply squares checked by `omega`.
- `formal/EndgameChess/Rules/KRKLive/Relocation.lean` (new):
  - the invariant `RookInv`, restored by every free reply;
  - `rook_move_ok` (prose (ii)) and `after_rook`;
  - the P1 branches `krk_home`, `krk_hfile`, `krk_rankToH` (HV, direct) and `krk_fs` (FS F1/F2/F3);
  - **`krk_P1`**: every normalised invariant state reaches a model mate.
- `formal/EndgameChess/Rules/KRKLive/Main.lean` (new):
  - `krk_live_of_not_check`;
  - **EC-C008(a)** `krk_strong_to_move_live`;
  - `lone_move_cases` and `reachK_cons`;
  - **EC-C008(b)** `krk_dead_iff` (no hypothesis on how `q` arose, so stronger than the prose);
  - `initial_not_KRK`, `arisen_krk_strong_live` and `krk_drawn_by_rule_iff` (Art. 5.2.2 characterisation for arisen K+R vs K);
  - non-vacuity examples: the RL-h exception stalemate, FS case F2, and (a) applied after a legal move.
- `formal/EndgameChess.lean`: 3 imports added. `formal/AxiomCheck.lean`: 23 new reports and 5 `#check`s appended.
- `audits/EC-C008_KRK_LIVE_LEAN.md`: completed (Part 2, Gate F evidence).
- Status notes: `research/CANDIDATES.md`, `proofs/EC-C008_KRK_LIVE.md`, `README.md`, `docs/ROADMAP.md` and `formal/README.md`.
- `NEXT_SESSION.md`: S023 installed (Gate Z).

## Notes on the formalisation
- **Replies.** The model is cooperative, so one explicit reply is chosen in each case. The continuation is proved for every state satisfying `RookInv`, which every free reply produces. So the "any reply" of the prose is covered.
- **RL-h's case split** is reorganised. It first asks whether `S` is ≥ 2 files or ≥ 2 ranks from `L`, so every reply is an explicit square. The statement is unchanged, and the only exception is still `(c8, h7, a8)`.
- **RL-f** needs `sx ≤ 3` explicitly; the prose assumes it through "`S` normalised". The proof is shorter than the prose's.
- **P1 legs 2 and 3** of the file shift reuse the HV lemma, because `S` is off the rook's new rank.
- **Performance.** A first draft decided `rook_move_ok` with a single `omega` over every disjunction, which took minutes. It was replaced by a structured proof (`shield_of_line`, `onSeg_trans`). `Reply.lean` still takes about 2 minutes, with `maxHeartbeats 4000000` (an elaboration budget only).

## Status
EC-C008: `LOCAL_VERIFIED → FORMAL_VERIFIED` (Gate F). Not frozen.

## Checks actually run
- `lake build` on the working tree: `Build completed successfully (22 jobs)`.
- `lake env lean AxiomCheck.lean`: exit 0; 161 reports, all ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `ofReduceBool`. Both main declarations give `[propext, Classical.choice, Quot.sound]`.
- **Fresh GitHub clone** of `ccr-65bb49c1-g989hw` at `a8bc161d2a51b92c340697af16a10e874cd9a098` (HEAD verified), empty `.lake`:
  - `lake build`: exit 0, `Build completed successfully (22 jobs)`, 3 min 47 s. The new modules took Basic 33 s, Endgame 7.4 s, Reply 127 s, Relocation 10 s and Main 1.3 s.
  - `lake env lean AxiomCheck.lean`: exit 0, with output byte-identical to the working-tree run (161 reports: 143 × the standard three, 5 × `[propext, Quot.sound]`, 8 × `[propext]`, the rest axiom-free).
  - Forbidden-token grep on the clone: 0 matches.
- Forbidden-token grep (`sorry|admit|axiom|unsafe|native_decide|implemented_by|extern`) on `Rules/KRKLive/*.lean`: 0 matches.
- Negative controls (scratch file): 3 false claims rejected (two by `decide`; one where `krk_RLh`'s `¬HExc` obligation cannot be discharged at `(c8, h7, a8)`).
- `python3 -m unittest discover -s tests`: `Ran 33 tests … OK`.
- `python3 scripts/validate_ledger.py`: `LEDGER VALID: 6 frozen theorem(s) (structure only)`.
- CI: not observed.

## Ledger effect
None. There are 6 frozen theorems; `theorems/LEDGER.csv` is unchanged.

## Installed next session
See `NEXT_SESSION.md` at this commit: S023, the Gate Z freeze of EC-C008 as EC-T0007.
