# S007 — Rules kernel K1: general position and FIDE Article 3 move model

**Date:** 2026-10-16
**Type:** Infrastructure session (rules kernel). No chess theorem; no ledger change.
**Base revision:** `a6ccb0a92ed035afc2819bfdae5977e743a0ab90` (`main`, S006).
**Kernel source commit:** `4f871bedc1006efbdba17e8f4feaa6a453659f09` (branch `claude/epic-goldberg-mrynfu`, merged to `main`).

## Changes
- **New Lean modules** in `formal/EndgameChess/Rules/`. They reuse the `KK` square and colour types and are imported from `formal/EndgameChess.lean`.
  - `Board.lean`: `PieceType`, `Piece`, `PromoPiece`, `allSquares` (`mem_allSquares`), square colour, `forward`, `homeRank`, `pawnRank`, `lastRank`, `dx`, `dy`.
  - `Position.lean`: `Position` (board, turn, castling rights, en-passant target), `initial`, `boardOf`, and `initial_wellFormed`.
  - `Moves.lean`: the move rules.
    - Attack, check and geometry: `isBetween`, `pathClear` (3.5), `attacksFrom`, `attacked`, `inCheck`.
    - Move legality: `targetOK` (3.1, 1.4.1), `pawnMoveOK` (3.7.1–3.7.3.2), `promoOK` (3.7.3.3), `canCastle` (3.8.2, 3.8.2.1, 3.8.2.2), `isPseudo`, `play` (with rights and e.p. update), `isLegal` (3.9.2, 3.10.1), and `Legal`.
    - Generator: `legalMoves` and `legalPositions`, with `mem_legalMoves` / `mem_legalPositions` (exactness).
    - Supporting results: `not_inCheck_after_legal`, `play_turn`, `legal_mover_safe`, and `perft`.
  - `Sanity.lean`: kernel `decide` theorems. They cover the 20 legal initial moves; en passant (legal, expired, pinned); promotion; castling (legal, through check, out of check, without the right, queen side with b1 attacked); pins; and no king capture.
- `formal/Checks/Perft.lean`: evaluation only, with a FEN reader. It runs perft on the Lean generator for 5 positions.
- `formal/AxiomCheck.lean`: 18 kernel `#print axioms` lines.
- `scripts/perft.py`: an independent 10×12 mailbox generator, plus FEN reader and published test positions. `tests/test_perft.py` checks depth ≤ 2.
- `docs/RULES_KERNEL.md`: the clause-by-clause FIDE → Lean bridge, with verbatim text and an open review sign-off row.
- `audits/EC-C004_K1.md`: the audit (evidence, perft table, mutation test, falsifications).
- Status files updated: `research/CANDIDATES.md` (EC-C004 K1 done, still `PROPOSED`), `docs/ROADMAP.md`, `README.md`, `formal/README.md`. `NEXT_SESSION.md` now holds S008 (K2).

## Findings, separated
- **Kernel-checked (Lean `decide`):** the facts in `Rules/Sanity.lean` and `Position.lean` listed above.
- **Proved (Lean):** generator exactness (`mem_legalPositions`); the mover is not in check after a legal move.
- **Evaluated / tested (supplementary):** perft agreement between Lean, Python and the published values (audit §1.2); mutation sensitivity (audit §1.3).
- **Not done:**
  - agreement with `LegalKK` / `KBK.Step` (S008);
  - reachability and Art. 5.2.2 (S009);
  - independent human review of `docs/RULES_KERNEL.md`.
- **Noted:** on the retrieved FIDE page, promotion is numbered 3.7.3.3–3.7.3.5, while its glossary cites 3.7.5.

## Checks actually run
- FIDE page retrieved with curl, HTML SHA-256 `c5b1692a…476f` (identical to S001's retrieval). The text was extracted for verbatim quotes.
- Fresh `git clone` from GitHub, checked out at `4f871bedc1006efbdba17e8f4feaa6a453659f09` with no `.lake`, then `cd formal && lake build`. Exit 0:
```
✔ [2/9] Built EndgameChess.KK (2.7s)
✔ [3/9] Built EndgameChess.Rules.Board (462ms)
✔ [4/9] Built EndgameChess.Rules.Position (772ms)
✔ [5/9] Built EndgameChess.Rules.Moves (730ms)
✔ [6/9] Built EndgameChess.KBK (13s)
✔ [7/9] Built EndgameChess.Rules.Sanity (23s)
✔ [8/9] Built EndgameChess (241ms)
Build completed successfully (9 jobs).
```
- `lake env lean AxiomCheck.lean`: 18 `EndgameChess.Rules.*` lines, each `[propext, Quot.sound]`, `[propext]`, or "does not depend on any axioms". EC-T0001/EC-T0002 lines are unchanged. The subset axiom gate passed.
- Forbidden-token grep over all `formal/**/*.lean` (including `Checks/`), excluding `.lake`: no matches.
- Frozen hashes: `KK.lean` `4843459c…09b1a0` and `KBK.lean` `c668e0c0…95c6d7`, both unchanged.
- Kernel module SHA-256 at `4f871be`:
  - `Board.lean` `c21144f5274cd4a4e023a7d868856a787c984cd5882e8e4e5d8ba2d015f2fdd1`
  - `Position.lean` `8544dbf23cb83798f83196366127a4afcd899da7d86689a10c23da3112447e7f`
  - `Moves.lean` `6a10be0387add5e891c1e53acd567f5a9f32701082ff83c20f02c3ca3ee65958`
  - `Sanity.lean` `8d161127e5143ed06aca030fb69466f40abfa1530e935a896c68caa38254538f`
- `lake env lean Checks/Perft.lean`: all counts OK (34 s). Deep run (evaluation, 7 min 26 s): Kiwipete perft(3) = 97,862, Position 4 perft(3) = 9,467 and Position 5 perft(3) = 62,379, all OK.
- `python3 scripts/perft.py 4`: all published values OK (2.8 s), including perft(4) = 197,281.
- Mutation test (scratch copies): 3, 3, 5 and 11 mismatches for the four broken rules.
- `python3 -m unittest discover -s tests`: all tests OK. `python3 scripts/validate_ledger.py`: `LEDGER VALID: 2 frozen theorem(s) (structure only)`.
- Remote CI (observed): `Lean build (EC formal proofs)` run 38911391098 on the kernel commit `4f871be` itself, conclusion **success**. https://github.com/jfairfaxball-348/engame-chess/actions/runs/38911391098

## Status and ledger effect
EC-C004: still `PROPOSED`, with K1 done. `theorems/LEDGER.csv` unchanged. Frozen theorems: **2**.

## Installed next session (full text of `NEXT_SESSION.md`)

> # NEXT SESSION — S008: Rules kernel K2 — agreement with the K vs K and K+B vs K models (closes G1)
>
> **Owner instruction:** Execute this S008 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C004 is `PROPOSED`. Do not treat this prompt as evidence that any agreement theorem exists.
>
> ## Context
> **S007 (K1)** built the general kernel `formal/EndgameChess/Rules/` (`Board`, `Position`, `Moves`, `Sanity`):
> - `isLegal`/`Legal`, and a generator proved complete and sound (`mem_legalPositions`);
> - 20 legal initial moves, kernel-checked;
> - worked examples (castling, en passant, promotion, pins);
> - perft agreement with an independent Python generator and with published values;
> - the bridge table `docs/RULES_KERNEL.md`.
>
> **K2 links the frozen bespoke models to the kernel.** The trust in move-set fidelity (gap **G1** in the EC-T0001/EC-T0002 manifests) then reduces to trust in the single kernel encoding.
>
> ## Objective
> New module `formal/EndgameChess/Rules/Agreement.lean`, which imports `EndgameChess.KK`, `EndgameChess.KBK` and `EndgameChess.Rules.Moves`.
>
> **Do not edit** `KK.lean` (SHA-256 `4843459c…09b1a0`), `KBK.lean` (`c668e0c0…95c6d7`) or the K1 kernel modules. If the kernel needs a fix, stop and install a remedial prompt: a kernel change would invalidate S007's evidence.
>
> ## Required work
> 1. **Embeddings.**
>    - `ofKK : KKState → Position`: a board with exactly two kings, the side to move, no castling rights, no en-passant target.
>    - `ofKBK : KBKState → Position`: the strong side's colour from `strongColour`, the bishop of that colour, the same flags.
>    - Matching `Pos → Position` for KBK's combined type.
> 2. **Agreement, K vs K.** For every `KKState` `a`, `b`: `KK.LegalKK a b ↔ Rules.Legal (ofKK a) (ofKK b)`.
>    - Also prove *closure*: every `Rules.Legal (ofKK a) q` has `q = ofKK b` for some `b`.
>    - State whether `a` needs to be admissible (distinct squares) and justify that choice. Junk states with `wk = bk` exist in `KKState`.
> 3. **Agreement, K+B vs K.** For `LKBK`-admissible `p` (or a stated, justified hypothesis): `KBK.Step (.kbk p) q ↔ Rules.Legal (ofKBK p) (embed q)`, including the bishop-capture branch into K vs K and the `kk` branch, together with closure.
>    - Key sub-lemmas:
>      - `Rules.attacked` on a KBK board equals `KBK.weakInCheck` / `strongInCheck`;
>      - `isBetween`/`pathClear` agree with `KBK.between`/`bishopAttacks` on diagonals;
>      - `targetOK`, `canCastle` and pawn clauses are vacuous on these boards.
> 4. **Deadness transfer.** Define kernel `Rules.Dead p := ¬ ∃ q, ReachK p q ∧ MatedK q`, with `MatedK q` meaning: side to move in check and no `Legal` successor. Then prove:
>    - `Rules.Dead (ofKK a) ↔ KK.Dead a` for admissible `a`;
>    - `Rules.Dead (ofKBK p) ↔ KBK.Dead (.kbk p)` for `LKBK p`.
>
>    Then derive kernel-level corollaries `kernel_dead_KK` and `kernel_dead_KBK` from the frozen EC-T0001/EC-T0002 theorems.
> 5. **Proof method.** Use structural and arithmetic reasoning (`omega`, case splits on `PieceType`, lemmas about `boardOf`/the embedding boards). Use `decide` only for closed finite facts. If a lemma needs a finite check over all 64 squares, keep it small and kernel-checked. No `native_decide`.
> 6. **Checks.** `lake build`; `#print axioms` for every new main declaration (add them to `AxiomCheck.lean`); forbidden-token grep; frozen-module hashes unchanged; a clean-checkout build of the proof commit.
> 7. **Audit** `audits/EC-C004_K2.md`. Map each agreement theorem to the gap it closes, check the hypotheses for hidden weakening (for example, an agreement that holds only on a vacuous class), and add non-vacuity examples.
> 8. **Status.** If steps 2–6 pass, EC-C004 part K2 is done. Keep EC-C004 `PROPOSED` until K3 also lands (S009). Record that G1 is closed *modulo the kernel bridge `docs/RULES_KERNEL.md`*, which still awaits independent human review.
>
> ## Closeout
> Write `sessions/S008_KERNEL_K2.md` and add a `sessions/SESSION_LEDGER.md` row, covering:
> - checks actually run, with verbatim outputs;
> - base and proof SHAs;
> - frozen-module hashes;
> - CI evidence;
> - ledger effect (none).
>
> Install **S009** in full. If K2 is incomplete, install a targeted remedial S008 instead.
>
> > **S009 — K3, reachability and rules.**
> > - Define `Arisen` as reachability from `Rules.initial` under `Legal`.
> > - Prove that every `Legal` move producing K vs K or K+B vs K material yields an admissible / `LKBK` position, whatever the predecessor. This closes **G2**.
> > - Prove that `Arisen` positions always have exactly one king per colour.
> > - Define `Rules.Outcome` encoding Art. 5.2.2 (dead ⇒ drawn immediately) as a named *rule definition, not a theorem*, and derive the draw corollaries. This makes **G3** explicit.
> > - Issue `v2.md` manifests for EC-T0001 and EC-T0002 with superseding ledger rows, keeping v1.
> >
> > After that: EC-C003 (K+N vs K), over the kernel.
>
> Then commit, push and merge to `main`.
