# Audit — EC-C008 Lean formalisation, part 1 (S021, partial)

**Subject:** `formal/EndgameChess/Rules/KRKLive/Basic.lean` and `formal/EndgameChess/Rules/KRKLive/Endgame.lean`, proof-source commit `a927566af9c6dc69e7661286e3eb5da1069c23ec`. **Prose:** [proofs/EC-C008_KRK_LIVE.md](../proofs/EC-C008_KRK_LIVE.md) (route v3).
**Auditor:** same session (S021). **Toolchain:** `leanprover/lean4:v4.35.0`, core only, run locally (Linux cloud container, elan).
**Status:** partial. EC-C008 stays `LOCAL_VERIFIED`. The main theorem `krk_strong_to_move_live` and the lemmas RL-h, RL-f and P1 are **not** formalised yet (S022).

## 1. Design: a geometric move model, transported to the kernel
The route chooses every move, for both sides, because `¬DeadK` asks only for *some* series of legal moves reaching mate. So Part 1 needs:
- **sufficient** conditions for the moves the route plays, and
- the **full** characterisation of the lone king's moves at the final mate.

These are packaged as a small model over `KRKState = (sk, rs, wk, strong-to-move)`:
- `StepM`: a rook move, a strong-king step or a non-capturing lone-king step, each with its geometric legality conditions. These are stated only through `dInf`, `RookLine` and `OnSeg` (coordinates).
- `MateM`: the rook checks, and every neighbour of the lone king is adjacent to the strong king, or is a non-rook square that the rook sees once the lone king stands on it.
- `WinM a`: a model mate is reachable by `StepM` moves.

The soundness theorems carry the model to the kernel for **any castling rights and en-passant target** (`Matches q σ a` constrains only the board and the turn):

| Lean | Content |
|---|---|
| `step_sound` | Each `StepM` move is a kernel `Legal` move to a matching position. The proof uses `isPseudo`, `play_board_simple`, `targetOK` and `inCheck_*_krk`. |
| `mate_sound` | `MateM` ⇒ kernel `MatedK`. Every kernel move of the side to move is a lone-king move: the only piece of that colour is its king, and castling is excluded by `canCastle_false_of_noRook`. The analysis includes the capture of the rook (`m.dst = rs`), after which the adjacent strong king gives check. |
| `chain_sound`, `not_deadK_of_winM` | A model path gives a kernel `ReachK` path, so `WinM a` and `Matches q σ a` ⇒ `¬DeadK q`. |

This splits the trust: the route lemmas are pure coordinate arithmetic, and their link to FIDE runs through the soundness lemmas and the kernel.

## 2. Statement correspondence (infrastructure, `Basic.lean`)
| Prose / task | Lean | Check |
|---|---|---|
| Rook moves along a clear line | `lineGeom_iff`, `isBetween_iff_onSeg`, `pathClear_iff`, `rook_attacks_krk` | On a rook line, the kernel's `isBetween` (collinearity plus additivity of `dInf`) is exactly the coordinate `OnSeg`. The products in `isBetween` are discharged by `Int.mul_eq_zero`. On `krkBoard` only the two kings can block, so the rook's attack is `RookSees rs t sk wk`. |
| `attacked` / `inCheck` on `krkBoard` | `attacked_krk`, `inCheck_weak_krk`, `inCheck_strong_krk` | Same shape as the frozen KNK lemmas. The lone king is in check iff the strong king is adjacent or the rook sees it. The strong king is in check iff the kings are adjacent (F2). |
| `Legal` via the board after a move | `play_board_simple` | Generalises `play_nrp` and `play_kingStep` to boards with a rook. The move must not be a pawn move, a promotion or a castling (king moves are single steps). The board update then holds whatever the flags. |
| F3 (flags only add moves) | `Matches` leaves flags free; `step_sound` | The route never castles, so flags do not matter for sufficiency. At the mate, the lone side has no rook, so it cannot castle. |
| F4 (reflections) | `BoardSym`, `symId`, `symX`, `symY`, `symXY`, `step_map`, `mate_map`, `winM_map`, `winM_of_sym`, `Normal`, `exists_sym_normal` | **Recorded choice:** reflection is proved for the model, not for the whole kernel. The kernel is *not* reflection-invariant: castling starts on the e-file and pawns move one way. Every model predicate is defined through reflection-invariant geometry, so `winM_of_sym` holds; `not_deadK_of_winM` then returns to the unreflected kernel position. `exists_sym_normal`: one of the four maps puts `S` at `sx ≤ 3`, `sy ≥ 2`. |

## 3. Statement correspondence (end-game half, `Endgame.lean`)
All statements quantify over arbitrary squares, with hypotheses on coordinates. No position is enumerated.

| Prose | Lean | Check |
|---|---|---|
| Tempo pairs and regions | `TempoPair` (`G`, `H`), `TempoPair.Mem`, `TempoPair.Region` | `G`: rook on rank 8, file g/h; region files a–f × ranks 1–7, minus `N1[S]` (`2 ≤ dInf sk s`). `H`: rook on the h-file, rank 7/8; region files a–g × ranks 1–6, minus `N1[S]`. |
| Tempo move legal; the step into the region is legal | `tempo_step`, `lone_step_region`, `TempoPair.no_line` | The rook's lines miss the region entirely, so blocking is never needed. The partner square is empty because `S` is on files a–d and `L` is in the region. |
| Lemma M | `krk_lemmaM` | Hypotheses: `L = (a,0)`, `S = (a,2)`, `r ≥ a+2`, `y ≥ 1`, strong side to move. The prose bound `a ≤ 4` is dropped: it follows from `r ≥ a+2` and `r ≤ 7`. The proof gives the rook move to `(r,0)` and `MateM` for **all** neighbours, with the escape `(a−1,0)` evaluated on the board after the move. |
| Lemma E | `krk_lemmaE_lone` (induction on `j`), `krk_lemmaE` | The rook is on a square of a pair `P`, `L = (a,j)`, `S = (a,j+2)`, `a ≤ 3`, `j ≤ 5`. The induction step is the lone king down one rank, then the strong king down one rank. The base is the shuttle `(a+1,0)`, a tempo move, back to `(a,0)`, then Lemma M. With the strong side to move: Lemma M if `j = 0`, otherwise a tempo move, then the lone-king form. Either side to move is covered. |
| Lemma C | `Conn`, `rect_minus_box_conn`, `krk_conn_region` | General form: rectangle `[x0,x1]×[y0,y1]` minus box `[bx0,bx1]×[by0,by1]`, with a column `c` and a row `ρ` of the rectangle that miss the box ("spans neither the full width nor the full height"). Every square is joined to `(c, ρ)` by unit rook steps (`conn_rank`, `conn_file`), split on whether the square's rank meets the box, as in the prose. Instances: `G` with `c` = file f, `ρ` = rank 1; `H` with `c` = file g, `ρ` = rank 1. `Conn` is symmetric and transitive. |
| Lemma W | `krk_lemmaW` | Induction on the `Conn` path from `L` to `T = (sx, sy−2)`. The path comes constructively from Lemma C. Each round is a tempo move, then the next step. At `T`, Lemma E applies. |
| Lemma S | `krk_lemmaS` | Hypotheses: rook on h8, strong side to move, `Normal sk`, kings apart, `L ≠ h8`, rook does not see `L`. The four cases are derived by `omega` from these hypotheses (so the case split is exhaustive): region `G`; g-file ranks 1–6 (region `H`); g7 (`Rh8–g8+`, `Kf6`); rank 8 shielded by `S` (`Rh8–g8`, `L` one rank down). |
| Corollary of §4 | `krk_settled_live` | Kernel form: `IsKRK q σ sk h8 wk`, `q.turn = σ`, `Normal sk`, `inCheck q σ.opp = false` ⇒ `¬DeadK q`, for any flags. |

## 4. Non-vacuity (`decide`)
- `krkM_mate_example`: White Kc3, Rh5, Black Kc1, White to move. The kernel generator itself confirms that Rh5–h1 is legal, that Black is then in check, and that `legalMoves = []`. This checks Lemma M's pattern without the model.
- `krkM_example`: the same position is `¬DeadK` **through** `krk_lemmaM` and `not_deadK_of_winM`.
- `krkS_rank8_example`: White Kd8, Rh8, Black Ka8, White to move (Lemma S case 4). `decide` shows Black is not in check; the position is `¬DeadK` via `krk_settled_live`.
- `krkS_g7_example`: White Kb3, Rh8, Black Kg7, White to move (Lemma S case 3). Same checks.
- **Negative control** (scratch file, not committed): `legalMoves (play mPos rh1) ≠ []` and `inCheck sRank8Pos .black = true` were both **rejected** by `decide` (2 errors, "decide proved that the proposition … is false").

## 5. Checks actually run (local)
- `lake env lean` on each new module: no errors, no warnings.
- `lake build` (working tree): `Build completed successfully (19 jobs)`.
- `lake env lean AxiomCheck.lean`: exit 0; 138 axiom reports (101 earlier + 37 new). Every report is ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `ofReduceBool`.
- Forbidden-token grep (`sorry|admit|axiom|unsafe|native_decide|implemented_by|extern`) on `Rules/KRKLive/*.lean`: no matches.
- Changed under `formal/`: two new modules, `EndgameChess.lean` (+2 imports), `AxiomCheck.lean` (appended). No frozen module was edited.
- **Fresh clone** of the session repository at `a927566af9c6dc69e7661286e3eb5da1069c23ec`, empty `.lake`: `lake build` exit 0 (19 jobs); `lake env lean AxiomCheck.lean` exit 0, with output byte-identical to the working-tree run.
- CI: not observed.

### Axiom report (new declarations)
```
'EndgameChess.Rules.lineGeom_iff' depends on axioms: [propext]
'EndgameChess.Rules.isBetween_iff_onSeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.pathClear_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.rook_attacks_krk' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.attacked_krk' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.inCheck_weak_krk' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.inCheck_strong_krk' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.play_board_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.legal_of_pseudo' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.winM_of_step' does not depend on any axioms
'EndgameChess.Rules.step_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.mate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.chain_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.not_deadK_of_winM' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.step_map' depends on axioms: [propext]
'EndgameChess.Rules.mate_map' depends on axioms: [propext]
'EndgameChess.Rules.winM_map' depends on axioms: [propext]
'EndgameChess.Rules.winM_of_sym' depends on axioms: [propext]
'EndgameChess.Rules.exists_sym_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.tempo_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.lone_step_region' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_lemmaM' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_lemmaE_lone' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_lemmaE' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.Conn.symm' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.Conn.trans' does not depend on any axioms
'EndgameChess.Rules.rect_minus_box_conn' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_conn_region' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_lemmaW' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_lemmaS' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_settled_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krkM_mate_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krkM_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krkS_rank8_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krkS_g7_example' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. What remains (S022) and notes for it
- **RL-h, RL-f, P1, the main theorem** `krk_strong_to_move_live` (EC-C008(a)) and **`krk_dead_iff`** (with EC-T0006).
- The model has everything P1 needs: rook moves along clear lines (`StepM.rook`), and the lone king's reply. Because the route lets the lone king play *any* non-capturing legal reply, P1 must be proved for every reply that satisfies the `StepM.lone` conditions. RL-h and RL-f give existence; the next leg needs only the invariants (ii)/(iii) of the prose, which `StepM.lone` provides (`¬RookSees` after the move).
- The "or it is checkmated" branches of RL-h and RL-f should be discharged into `MateM`, so that `winM_of_mate` closes them.
- The main theorem: from `Legal p q` derive the kings apart (F1) and the lone king not in check. Take a symmetry from `exists_sym_normal`, run P1 in the normal frame, finish with `krk_lemmaS`, and transfer with `winM_of_sym` and `not_deadK_of_winM`.
- P1's exception `(S, R, L) = (c8, h7, a8)` and the file-shift branch must be stated as schemas, not cases.

## 7. Residual assumptions
A1; the kernel encoding (human review of `docs/RULES_KERNEL.md` still open); the audit is by the same agent.
