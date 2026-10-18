# Audit — EC-C003 K+N vs K, Lean formalisation over the rules kernel (S012)

**Subject:** `formal/EndgameChess/Rules/KNK.lean`, proof-source commit `3adcebbb4ae643a62c8bf18b478bf70da774dbf8`.
**Prose source:** [proofs/EC-C003_KNK.md](../proofs/EC-C003_KNK.md) (Gate L, S011).
**Auditor:** same session as the formalisation (S012). No independent second reader yet.
**Toolchain:** `leanprover/lean4:v4.34.1` (Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core only, `lake-manifest.json` has no packages. Run **locally** on the owner's machine (Windows, elan default toolchain).

## 1. Statement correspondence
| Prose | Lean | Check |
|---|---|---|
| `IsKNK q σ K N k`: three distinct squares, board exactly σ king, σ knight, σ̄ king; turn and flags arbitrary | `IsKNK`, `knkBoard` | Same shape as the frozen `IsKBK`/`kbkBoard`. Constrains only `q.board`; `turn`, `castling`, `ep` are free. |
| Theorem: `Legal p q ∧ IsKNK q … ⇒ DeadK q`, any `p`, either σ | `dead_of_legal_into_KNK` | `p` is an arbitrary kernel position (any material); `σ` is universally quantified, so both orientations. |
| Arisen form | `arisen_KNK_dead` (`Arisen q := ReachK initial q`) | Uses `initial_not_KNK` (a2 holds a pawn) for the length-0 case. |
| 5.2.2 corollary | `knk_drawn_by_rule` (`Rule5_2_2` from frozen `Outcome.lean`) | Visibly depends on the named rule encoding. |
| N0 | `kings_apart_of_legal`, `strong_not_inCheck` | From `legal_mover_safe`, splitting on which colour moved (`colour_cases`). |
| N1(a–c) | `knightGeom_iff`, `knight_not_orth`, `ne_of_knight_adj` | `omega` on coordinate differences; no enumeration. |
| N2 | `escape_square` (geometry), `weak_has_move` (kernel move `wk → s`) | The `h` (same rank) / `v` (same file) construction via `exists_adj`; `exists_adj` is `decide` over `Fin 8` only. Legality is shown through `isPseudo_of_king`, `play_nrp` and `inCheck_weak_knk` on the resulting `knkBoard σ K N s`. |
| N3 | `step_closed` | Generic `play_nrp` board update; `targetOK` excludes landing on either king and on own pieces; the lone-king capture of the knight yields `IsKK` (colour split on σ). |
| N4 | `reach_cases`, `not_mated_KNK` | Induction on `ReachK`. Once a K vs K position is entered by a legal move, the frozen `dead_of_legal_into_KK` (EC-T0003) covers every continuation, so no K vs K closure is re-proved. |

**Deviation from the S011 plan (harmless):** the plan proposed a class `C(r)` closed under both K+N vs K and K vs K steps. The Lean proof instead records "reachable from a K vs K position produced by a legal move" and lets EC-T0003 handle everything after the capture. This is a weaker invariant needing less work; the theorem statement is exactly the planned one.

## 2. Non-vacuity (all by `decide`)
- `knight_check_example`: White Kc6, Na4, Black Ka8, White to move; **Nb6+ is legal**, produces `IsKNK` with Black in check, and the result is `DeadK` by the main theorem. So the hypothesis is satisfiable with a knight check.
- `knk_stalemate_example`: Black Ka8, White Kb6 + Nc6, Black to move: not in check, `legalMoves = []`. Stalemate is in the class.
- `knight_capture_example`: Black Kb2xc3 (White Kh8) is legal and produces `IsKK`: the capture branch is live.
- Existing kernel evidence that `MatedK` is satisfiable elsewhere (K2/K3 audits) stands; the theorem is not vacuous by an unsatisfiable mate predicate.

## 3. Checks actually run (local)
- `lake env lean EndgameChess/Rules/KNK.lean`: no errors, no warnings.
- `lake build` (incremental, working tree): `Built EndgameChess.Rules.KNK (7.6s)`, `Build completed successfully (16 jobs)`.
- **Clean checkout:** fresh `git clone` at `3adcebbb4ae643a62c8bf18b478bf70da774dbf8`, empty `.lake`, `lake build`: `Build completed successfully (16 jobs)` in 39.5 s (log below).
- `lake env lean AxiomCheck.lean` (clean checkout): exit 0; 92 axiom reports, every one ⊆ `[propext, Classical.choice, Quot.sound]`; 0 occurrences of `sorryAx` or `Lean.ofReduceBool`. EC-C003 lines in §4.
- Forbidden tokens in `KNK.lean` (`sorry|admit|axiom |unsafe|native_decide|implemented_by|extern`): none.
- Frozen modules: `git status` shows only `Rules/KNK.lean` (new), `EndgameChess.lean` (one import line) and `AxiomCheck.lean` (appended) changed under `formal/`. No frozen module edited; all of them rebuilt in the clean checkout.
- CI: not observed in this session.

### Clean-checkout build log
```
✔ [2/16] Built EndgameChess.KK (2.0s)
✔ [3/16] Built EndgameChess.Rules.Board (764ms)
✔ [4/16] Built EndgameChess.Rules.Position (797ms)
✔ [5/16] Built EndgameChess.Rules.Moves (877ms)
✔ [6/16] Built EndgameChess.KBK (9.2s)
✔ [7/16] Built EndgameChess.Rules.Sanity (14s)
✔ [8/16] Built EndgameChess.Rules.Lemmas (14s)
✔ [9/16] Built EndgameChess.Rules.AgreeKK (1.0s)
✔ [10/16] Built EndgameChess.Rules.AgreeKBK (8.4s)
✔ [11/16] Built EndgameChess.Rules.Flags (834ms)
✔ [12/16] Built EndgameChess.Rules.Reach (840ms)
✔ [13/16] Built EndgameChess.Rules.Outcome (611ms)
✔ [14/16] Built EndgameChess.Rules.KNK (7.6s)
✔ [15/16] Built EndgameChess (608ms)
Build completed successfully (16 jobs).
real	0m39.458s
user	0m0.015s
sys	0m0.015s
```

## 4. Axiom report (EC-C003 declarations, clean checkout)
```
'EndgameChess.Rules.dead_of_legal_into_KNK' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.arisen_KNK_dead' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.knk_drawn_by_rule' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.initial_not_KNK' depends on axioms: [propext]
'EndgameChess.Rules.weak_has_move' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.escape_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.knight_not_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.ne_of_knight_adj' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.kings_apart_of_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.strong_not_inCheck' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.step_closed' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.reach_cases' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.not_mated_KNK' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.inCheck_weak_knk' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.inCheck_strong_knk' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.knight_check_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.knk_stalemate_example' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.knight_capture_example' depends on axioms: [propext, Quot.sound]
```

## 5. Trust boundary
Lean checks the theorem about the kernel. Trusted and unchecked: A1; the kernel's encoding of Article 3 (`docs/RULES_KERNEL.md`, human review still open); the reading of 5.2.2 in `Rule5_2_2`; the Lean kernel, toolchain binary and standard axioms. **No gap found.** Verdict: Gate F passes, subject to the same-session caveat.
