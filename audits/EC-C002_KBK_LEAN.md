# Audit — EC-C002 Lean formalisation fidelity (S005)

**Subject:** `formal/EndgameChess/KBK.lean` (namespace `EndgameChess.KBK`), checked against [proofs/EC-C002_KBK.md](../proofs/EC-C002_KBK.md).
**Toolchain:** `leanprover/lean4:v4.34.1`, core only, no dependencies.
**Imports:** the frozen `EndgameChess.KK` (EC-T0001). It is unmodified: SHA-256 `4843459ca26af93e15e5894a9f32183d46f8c554132e81051c1c21140509b1a0`, identical to the manifest.
**Auditor:** the same session as the formalisation. No independent second reader.

## 1. Definition map

| Prose | Lean | Note |
|---|---|---|
| strong side `σ`, weak side `ω` | `Side`, `KBKState.strongColour` | Colour names matter only when embedding into `KKState` (`toKK` puts the strong king in its own colour's slot). Both orientations are covered by `strongColour : Colour`. |
| configuration `(K, X, k, t)` | `KBKState` (`sk`, `bs`, `wk`, `turn`) | Distinctness is part of `LKBK`, not of the type. |
| diagonal of `X` | `onDiag X q := X ≠ q ∧ \|Δx\| = \|Δy\|` | |
| strictly between on the diagonal | `between X r q := onDiag X r ∧ onDiag r q ∧ dInf X r + dInf r q = dInf X q` | Arithmetic form. Python cross-check against square-by-square ray walking (§3.1): **0 mismatches**. |
| bishop attack, 3.1.2 + 3.2 + 3.5 | `bishopAttacks occ X q := onDiag X q ∧ ∀ r, between X r q → ¬ occ r` | `occ` = the two kings (`kingsOcc`), the only possible blockers. The bishop's own square is an endpoint, not "between". |
| `InCheck` (3.9.1) | `weakInCheck` (strong king ∨ bishop), `strongInCheck` (weak king) | The bishop's attack uses the occupancy of that position. |
| `LKBK` | pairwise distinct ∧ ¬ the side not to move in check | |
| `AdmKK` | EC-T0001 `Admissible` | |
| legal moves (3.1–3.9, 1.4.1) | `Step`, five constructors: `strongKing`, `bishop`, `weakKing`, `weakCaptures`, `kk` | Each states 3.9.2 literally, as "the mover is not in check in the resulting state". The exception is `weakCaptures`, where only the strong king remains and the condition is `¬ kingAttacks sk bs` (the bishop has gone). |
| class `LKBK ∪ AdmKK` | `Closed : Pos → Prop` | |
| `Checkmate` | `Mated`: on `kbk`, the side to move is in check and has no `Step`; on `kk`, EC-T0001 `Checkmate` of either colour | On `kk`, `Step` is exactly `LegalKK`, so the two notions of "no move" agree. |
| `Reach`, `Dead` | inductive `Reach` over `Pos`; `Dead p := ¬∃ q, Reach p q ∧ Mated q` | ∀ paths, no stopping rule |

## 2. Theorem map

| Prose | Lean |
|---|---|
| B1a / B1b | `colour_of_bishopAttacks`, `colour_orth_neighbour` |
| B0′ | `kings_apart_of_LKBK`, `strong_not_inCheck_of_LKBK` |
| B2 (key) | **`weak_has_move_of_inCheck`**, via `exists_orth_neighbours` and `weak_step_of_far`: the explicit `h`/`v` construction, with no enumeration |
| capture → AdmKK | `admissible_of_capture` |
| B3 | `closed_of_step`; the `kk` branch is EC-T0001 `admissible_of_legal_step` |
| B4 | `closed_of_reach` (induction, length 0 included) |
| B5 | `not_mated_of_closed`; the `kk` branch is EC-T0001 `not_inCheck_of_admissible` |
| Theorem | **`dead_of_LKBK`**, `dead_of_closed` |
| B0 (in-model last move) | `LKBK_of_step`, `dead_of_step` |
| non-vacuity | `bishop_check_exists`, `stalemate_exists`, `mated_satisfiable` |

The proof chain `dead_of_LKBK → dead_of_closed → closed_of_reach / not_mated_of_closed → weak_has_move_of_inCheck` uses `omega`, `simp` and case analysis only. `decide` appears only in the three concrete examples, on closed propositions. There is no `native_decide`.

## 3. Attempted falsifications / surrogate checks
1. **`between` is faithful.** A script (scratchpad, not committed) compared the arithmetic `between` with explicit ray walking for every `X, q` on a common diagonal and every `r ∈ S`. It checked 35,840 diagonal pairs (each against all 64 `r`) and found 0 mismatches.
2. **Obstruction is modelled.** Both bishop moves and bishop checks require `∀ r, between → ¬ occ r`.
   - A move onto a king square is excluded (`s ≠ p.sk`, `s ≠ p.wk`).
   - Capturing the king is not possible (1.4.1).
   - The weak king's step is checked against `kingsOcc p.sk s`, the *new* occupancy, which covers X-rays through the vacated square.
3. **Move set complete.** Every piece and move kind is present: strong king, bishop, weak king (quiet), weak king takes bishop. There is no castling (no rook), no pawn moves, and no strong capture of the king. A *smaller* relation would weaken the theorem; this one mirrors the prose L3a-style analysis (proof B3).
4. **Capture branch.** `weakCaptures` leads to `kk` with the strong side to move. `admissible_of_capture` proves the kings are ≥ 2 apart, using `sk ≠ bs` from `LKBK`.
5. **Turn handling.** Every `kbk` constructor flips `turn`. `weakCaptures` sets the KK turn to `strongColour`.
6. **`Mated` is not vacuous.** `mated_satisfiable` gives weak Ka1, strong Kb2 (adjacent, so not `LKBK`), weak to move: checkmate.
7. **`Step` is not vacuous, and the theorem does not assume a move always exists.** `stalemate_exists` (Ka8 / Kb6 + Bc7) shows stalemates exist and are not `Mated`. `bishop_check_exists` shows bishop checks exist, so B2 is not vacuous.
8. **`Dead` quantifier.** `¬∃ q, Reach p q ∧ Mated q` covers every finite path and both sides.
9. **Frozen module untouched.** The KK.lean hash matches the EC-T0001 manifest.
10. **Trusted base.** `#print axioms` for each of the 16 KBK declarations reports `[propext, Classical.choice, Quot.sound]`, the subset `[propext, Quot.sound]`, or none (`LKBK_of_step`). These are all standard Lean axioms. CI was adjusted to accept any subset of the standard three, and it still rejects others: a negative test with `Lean.ofReduceBool` fails the gate.

## 4. Residual gaps (prose only)
1. A1. The reading of 3.1.2 + 3.2 + 3.5 as `bishopAttacks`. The identification of `Step` with the FIDE-legal moves.
2. **General B0:** a KBK position may arise by a capture from larger material. `LKBK_of_step` covers only KBK predecessors; the general case rests on the prose (3.9.2 applied to the last move).
3. The 5.2.2 normative consequence.

**Verdict:** within scope, the formal statements are faithful, and the main theorem is proved by the invariant argument. Gate F status depends on the clean-checkout build recorded in the S005 closeout.
