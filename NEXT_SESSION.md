# NEXT SESSION — S007: Rules kernel K1 — general position and FIDE Article 3 move model

**Owner instruction:** Execute this S007 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. Do not treat this prompt as evidence that the kernel exists.

## Why (owner decision, 2026-10-16)
EC-T0001 and EC-T0002 each trust a bespoke move relation (`KK.LegalKK`, `KBK.Step`). Their manifests list three prose-only gaps:
- **G1:** move-set fidelity — does the bespoke relation match FIDE's legal moves?
- **G2:** positions reached by a capture from larger material.
- **G3:** the Article 5.2.2 rule step.

The rules-kernel track replaces many bespoke relations with **one** general, auditable encoding of FIDE Article 3:
- **K1 (this session):** the model.
- **K2 (S008):** agreement with `LegalKK` / `KBK.Step`; closes G1.
- **K3 (S009):** reachability, an explicit 5.2.2 rule definition, and v2 manifests; closes G2 and makes G3 explicit.

Candidate: **EC-C004** (`PROPOSED`).

## Objective
Build a faithful Lean 4 encoding of FIDE 2023 Articles 2–3 (initial position; legal moves) as new library modules. Back it with a clause-by-clause prose bridge and independent sanity evidence. **No agreement theorems yet; no ledger change; EC-C004 stays `PROPOSED`.**

## Non-negotiable constraints
- **Do not edit** `formal/EndgameChess/KK.lean` (SHA-256 `4843459c…09b1a0`) or `formal/EndgameChess/KBK.lean` (SHA-256 `c668e0c0…95c6d7`). Both are frozen. Verify the hashes at closeout.
- Use the same toolchain, `leanprover/lean4:v4.34.1`, core only. No `sorry`, `admit`, custom `axiom`, `unsafe` or `native_decide` in library modules.
  - Kernel `decide` is allowed only for small closed facts.
  - If a fact such as a move count is too slow for the kernel, prove it another way, or state it in a separately labelled non-library `Checks/` file that is excluded from axiom-gated declarations, and say so.
- Rule text: FIDE Laws of Chess effective 1 January 2023, https://handbook.fide.com/chapter/E012023. Retrieve the page, and quote the text verbatim in comments and in the bridge document. Record the retrieval date.
- No tablebases or engine oracles. Public perft counts from the initial position (20, 400, 8,902) are elementary combinatorial facts and may be cited as cross-check targets. They are not evidence about endgames.
- Verify only the obligation (`AGENTS.md`): the new modules. CI builds incrementally.

## Required work
1. **Modules.** Place them under `formal/EndgameChess/Rules/` and import them from `formal/EndgameChess.lean`.
   - **`Board.lean`** — squares, `Colour`, `PieceType` (K, Q, R, B, N, P), `Piece`.
     - Either reuse `EndgameChess.KK.Square`/`Colour` directly, or define your own and prove a bijection. Reuse is preferred, so that K2 is simpler.
     - Include square colour (Art. 2.1), ranks/files, and the relative rank per colour.
   - **`Position.lean`** — the position state:
     - board as `Square → Option Piece`;
     - side to move;
     - castling-rights flags (for 3.8.2.1);
     - en-passant target `Option Square` (for 3.7.3.1).

     Also define the initial position (Art. 2.3).
   - **`Moves.lean`** — the move model. Every clause carries an Article-number comment with the verbatim text.
     - Attack, per 3.1.2 and 3.1.3.
     - Pseudo-moves for each piece: 3.2 bishop, 3.3 rook, 3.4 queen, with 3.5 obstruction; 3.6 knight; 3.7 pawn (single and double advance, diagonal capture, en passant 3.7.3, promotion 3.7.5 to Q/R/B/N of the same colour); 3.8.1 king; 3.8.2 castling with every condition in 3.8.2.1 and 3.8.2.2.
     - Captures (3.1.1), and the no-own-piece rule (3.1).
     - No king capture (1.4.1).
     - The self-check filter (3.9.2), using `inCheck` (3.9.1).
     - Update of castling rights and en-passant target after each move.
     - The relation `Legal : Position → Position → Prop`, or a move type with `apply`. Note that 3.10.1 defines "legal".

     Prefer a decidable, computable move generator `legalMoves : Position → List Position`, with a theorem relating it to the `Prop` relation. A computable generator makes later checks possible.
2. **Prose bridge `docs/RULES_KERNEL.md`.** A table with one row per Article sub-clause of 1.4.1, 2.x, 3.1–3.10, giving:
   - the verbatim FIDE text;
   - the Lean declaration or clause that encodes it;
   - any interpretation choice. A1 ("adjoining") is one example; the en-passant timing in 3.7.3.2 and promotion as "part of the same move" are others.

   State clearly that **this table is the single trusted FIDE→Lean bridge** for every theorem stated over the kernel, and that it needs an independent human review. Leave a sign-off line for the reviewer.
3. **Sanity theorems** (in `Rules/` or `Checks/`):
   - the initial position is well formed: 32 pieces, one king per colour, White to move, all castling rights, no en-passant target;
   - after any legal move, the mover is not in check;
   - the initial position has exactly 20 legal moves, preferably via the computable generator plus its correctness theorem;
   - one example each, proved, of en passant, promotion, castling, and illegal castling through check.
4. **Independent cross-check.** Write `scripts/perft.py`, a move generator written independently of the Lean code from the same FIDE text. Count perft(1..3) = 20, 400, 8,902 from the initial position. If feasible, run the Lean generator to the same depth (via `#eval` in a `Checks/` file, labelled as evaluation, not proof) and compare. Add a unit test for depth ≤ 2, kept fast.
5. **Audit `audits/EC-C004_K1.md`** — a hostile review of the encoding:
   - castling edge cases: rights, attacked squares, and pieces between;
   - en passant: only immediately after the double step, and never when it exposes the king;
   - promotion choices;
   - pins and discovered check;
   - the king never captured;
   - the non-vacuity of `Legal`.

   Record attempted falsifications and their outcomes.

## Closeout
Write `sessions/S007_KERNEL_K1.md` and add a `sessions/SESSION_LEDGER.md` row, recording:
- the changes;
- the checks that were actually run, with verbatim outputs;
- the base SHA and result SHA;
- the frozen-module hashes, unchanged;
- CI evidence, if observed;
- the status of EC-C004 (still `PROPOSED`);
- the ledger effect (none).

Install **S008** in full in `NEXT_SESSION.md` and in the closeout:

> **S008 — K2, agreement:** define embeddings `KKState → Position` and `KBKState → Position`, plus the inverse on positions with that material. Prove that on K vs K positions the kernel `Legal` corresponds exactly to `KK.LegalKK`, in both directions. Prove that on K+B vs K / K vs K positions it corresponds exactly to `KBK.Step`, including the capture branch. Derive `KK.Dead` ⇔ kernel-dead and `KBK.Dead` ⇔ kernel-dead on those classes. This closes **G1**.

Also outline S009 as below. If K1 is incomplete, install a targeted remedial S007 instead.

> **S009 — K3, reachability and rules:**
> - Define `Arisen` as reachability from the initial position under `Legal`.
> - Prove that every `Legal` move producing K vs K or K+B vs K material yields `Admissible` / `LKBK`, whatever the predecessor. This closes **G2**.
> - Define `Rules.Outcome` encoding Art. 5.2.2 (dead ⇒ drawn immediately) as a *named rule definition, not a theorem*, and derive the draw corollaries. This makes **G3** explicit.
> - Issue `v2.md` manifests for EC-T0001 and EC-T0002 with superseding ledger rows, keeping v1.
>
> After that: EC-C003 (K+N vs K), built over the kernel.

Then commit, push and merge to `main`.
