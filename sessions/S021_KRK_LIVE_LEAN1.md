# S021 — EC-C008 Lean formalisation, part 1 (infrastructure and end-game half)

**Date:** 2026-10-18
**Type:** Formalisation session (Gate F work, partial). No freeze.
**Base revision:** `a5948e3` (`main` after S020).
**Lean proof-source commit:** `a927566af9c6dc69e7661286e3eb5da1069c23ec`. The closeout commit follows it.

## Changes
- `formal/EndgameChess/Rules/KRKLive/Basic.lean` (new), the infrastructure:
  - rook geometry in coordinates (`RookLine`, `OnSeg`, `RookSees`), bridged to the kernel's `lineGeom`, `isBetween` and `pathClear`;
  - `attacked` and `inCheck` on `krkBoard`;
  - `play_board_simple`, the board after a non-pawn, non-promotion, non-castling move;
  - the KRK move model `StepM`/`MateM`/`WinM`, with kernel soundness (`step_sound`, `mate_sound`, `not_deadK_of_winM`) for any castling rights and en-passant target;
  - F4: `BoardSym` (identity, x-, y- and xy-reflections), `winM_of_sym` and `exists_sym_normal`.
- `formal/EndgameChess/Rules/KRKLive/Endgame.lean` (new), the end-game half:
  - tempo pairs `G`/`H` with their regions, the tempo move and the region step;
  - Lemma M (`krk_lemmaM`);
  - Lemma E (`krk_lemmaE_lone`, by induction on `j`; `krk_lemmaE`);
  - Lemma C (`rect_minus_box_conn`, a general rectangle minus a box; instance `krk_conn_region`);
  - Lemma W (`krk_lemmaW`, by induction on the Lemma C path);
  - Lemma S (`krk_lemmaS`);
  - the kernel corollary `krk_settled_live`;
  - non-vacuity examples by `decide`.
- `formal/EndgameChess.lean`: two imports added. `formal/AxiomCheck.lean`: 37 new reports and 3 `#check`s appended.
- `audits/EC-C008_KRK_LIVE_LEAN.md` (new): a partial Lean audit.
- Status notes: `proofs/EC-C008_KRK_LIVE.md` (status line), `research/CANDIDATES.md`, `README.md`, `docs/ROADMAP.md` and `formal/README.md`.
- `NEXT_SESSION.md`: S022 installed.

## Design decision (recorded)
F4 is proved for the **KRK move model**, not for the whole kernel. The kernel is not reflection-invariant: castling starts on the e-file and pawns move in one direction. The model's predicates use only `dInf`, `RookLine` and `OnSeg`, which every reflection preserves. Model paths go to kernel `ReachK` paths through the soundness lemmas, whatever the flags. This was the fallback the prompt allowed ("state the lemmas for the normalised frame only, and record that choice"), in a stronger form: the lemmas are stated in the normal frame, and the transfer back is proved.

## What is formalised and what remains
| Prose item | Status |
|---|---|
| Infrastructure: `Legal`, `attacked` and `inCheck` on `krkBoard`, F2, F3, F4 | **formalised** |
| Lemmas M, E, C, W and S; corollary "rook on h8 ⇒ live" | **formalised** (`krk_settled_live`) |
| RL-h, RL-f, P1 (relocation) | open (S022) |
| F1 from `Legal p q`, main theorem `krk_strong_to_move_live` (a), `krk_dead_iff` (b) | open (S022) |

EC-C008 stays **`LOCAL_VERIFIED`**.

## Checks actually run (local, Linux container, Lean v4.35.0 via elan)
- `lake build` on the working tree: `Build completed successfully (19 jobs)`.
- `lake env lean AxiomCheck.lean`: exit 0; 138 reports, all ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `ofReduceBool`. The new declarations are listed verbatim in the audit §5.
- **Fresh clone at `a927566`, empty `.lake`:** `lake build` exit 0 (19 jobs); `AxiomCheck` exit 0, byte-identical to the working-tree output.
- Forbidden-token grep (`sorry|admit|axiom|unsafe|native_decide|implemented_by|extern`) on `Rules/KRKLive/*.lean`: 0 matches.
- Negative control (scratch file): two false `decide` claims were rejected.
- `python3 -m unittest discover -s tests`: `Ran 33 tests … OK`.
- `python3 scripts/validate_ledger.py`: `LEDGER VALID: 6 frozen theorem(s) (structure only)`.
- CI: not observed.

## Ledger effect
None. There are 6 frozen theorems; `theorems/LEDGER.csv` is unchanged.

## Installed next session
See `NEXT_SESSION.md` at this commit: S022, EC-C008 Lean part 2 (RL-h, RL-f, P1, main theorem, `krk_dead_iff`), then Gate F.
