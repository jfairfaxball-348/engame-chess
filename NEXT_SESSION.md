# NEXT SESSION — S008: Rules kernel K2 — agreement with the K vs K and K+B vs K models (closes G1)

**Owner instruction:** Execute this S008 session when the owner says "run next session" in the context of this repository or pastes/links this prompt. Follow `AGENTS.md` first: fetch, start from the latest `main`, merge any unmerged session branch, and end by committing, pushing and merging to `main`. EC-C004 is `PROPOSED`. Do not treat this prompt as evidence that any agreement theorem exists.

## Context
**S007 (K1)** built the general kernel `formal/EndgameChess/Rules/` (`Board`, `Position`, `Moves`, `Sanity`):
- `isLegal`/`Legal`, and a generator proved complete and sound (`mem_legalPositions`);
- 20 legal initial moves, kernel-checked;
- worked examples (castling, en passant, promotion, pins);
- perft agreement with an independent Python generator and with published values;
- the bridge table `docs/RULES_KERNEL.md`.

**K2 links the frozen bespoke models to the kernel.** The trust in move-set fidelity (gap **G1** in the EC-T0001/EC-T0002 manifests) then reduces to trust in the single kernel encoding.

## Objective
New module `formal/EndgameChess/Rules/Agreement.lean`, which imports `EndgameChess.KK`, `EndgameChess.KBK` and `EndgameChess.Rules.Moves`.

**Do not edit** `KK.lean` (SHA-256 `4843459c…09b1a0`), `KBK.lean` (`c668e0c0…95c6d7`) or the K1 kernel modules. If the kernel needs a fix, stop and install a remedial prompt: a kernel change would invalidate S007's evidence.

## Required work
1. **Embeddings.**
   - `ofKK : KKState → Position`: a board with exactly two kings, the side to move, no castling rights, no en-passant target.
   - `ofKBK : KBKState → Position`: the strong side's colour from `strongColour`, the bishop of that colour, the same flags.
   - Matching `Pos → Position` for KBK's combined type.
2. **Agreement, K vs K.** For every `KKState` `a`, `b`: `KK.LegalKK a b ↔ Rules.Legal (ofKK a) (ofKK b)`.
   - Also prove *closure*: every `Rules.Legal (ofKK a) q` has `q = ofKK b` for some `b`.
   - State whether `a` needs to be admissible (distinct squares) and justify that choice. Junk states with `wk = bk` exist in `KKState`.
3. **Agreement, K+B vs K.** For `LKBK`-admissible `p` (or a stated, justified hypothesis): `KBK.Step (.kbk p) q ↔ Rules.Legal (ofKBK p) (embed q)`, including the bishop-capture branch into K vs K and the `kk` branch, together with closure.
   - Key sub-lemmas:
     - `Rules.attacked` on a KBK board equals `KBK.weakInCheck` / `strongInCheck`;
     - `isBetween`/`pathClear` agree with `KBK.between`/`bishopAttacks` on diagonals;
     - `targetOK`, `canCastle` and pawn clauses are vacuous on these boards.
4. **Deadness transfer.** Define kernel `Rules.Dead p := ¬ ∃ q, ReachK p q ∧ MatedK q`, with `MatedK q` meaning: side to move in check and no `Legal` successor. Then prove:
   - `Rules.Dead (ofKK a) ↔ KK.Dead a` for admissible `a`;
   - `Rules.Dead (ofKBK p) ↔ KBK.Dead (.kbk p)` for `LKBK p`.

   Then derive kernel-level corollaries `kernel_dead_KK` and `kernel_dead_KBK` from the frozen EC-T0001/EC-T0002 theorems.
5. **Proof method.** Use structural and arithmetic reasoning (`omega`, case splits on `PieceType`, lemmas about `boardOf`/the embedding boards). Use `decide` only for closed finite facts. If a lemma needs a finite check over all 64 squares, keep it small and kernel-checked. No `native_decide`.
6. **Checks.** `lake build`; `#print axioms` for every new main declaration (add them to `AxiomCheck.lean`); forbidden-token grep; frozen-module hashes unchanged; a clean-checkout build of the proof commit.
7. **Audit** `audits/EC-C004_K2.md`. Map each agreement theorem to the gap it closes, check the hypotheses for hidden weakening (for example, an agreement that holds only on a vacuous class), and add non-vacuity examples.
8. **Status.** If steps 2–6 pass, EC-C004 part K2 is done. Keep EC-C004 `PROPOSED` until K3 also lands (S009). Record that G1 is closed *modulo the kernel bridge `docs/RULES_KERNEL.md`*, which still awaits independent human review.

## Closeout
Write `sessions/S008_KERNEL_K2.md` and add a `sessions/SESSION_LEDGER.md` row, covering:
- checks actually run, with verbatim outputs;
- base and proof SHAs;
- frozen-module hashes;
- CI evidence;
- ledger effect (none).

Install **S009** in full. If K2 is incomplete, install a targeted remedial S008 instead.

> **S009 — K3, reachability and rules.**
> - Define `Arisen` as reachability from `Rules.initial` under `Legal`.
> - Prove that every `Legal` move producing K vs K or K+B vs K material yields an admissible / `LKBK` position, whatever the predecessor. This closes **G2**.
> - Prove that `Arisen` positions always have exactly one king per colour.
> - Define `Rules.Outcome` encoding Art. 5.2.2 (dead ⇒ drawn immediately) as a named *rule definition, not a theorem*, and derive the draw corollaries. This makes **G3** explicit.
> - Issue `v2.md` manifests for EC-T0001 and EC-T0002 with superseding ledger rows, keeping v1.
>
> After that: EC-C003 (K+N vs K), over the kernel.

Then commit, push and merge to `main`.
