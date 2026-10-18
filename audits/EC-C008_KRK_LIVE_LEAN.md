# Audit — EC-C008 Lean formalisation over the rules kernel (S021–S022, Gate F)

**Subject:** `formal/EndgameChess/Rules/KRKLive/{Basic,Endgame,Reply,Relocation,Main}.lean`. **Prose:** [proofs/EC-C008_KRK_LIVE.md](../proofs/EC-C008_KRK_LIVE.md) (route v3).
- **Part 1 (S021):** `Basic.lean` and `Endgame.lean`, proof-source commit `a927566af9c6dc69e7661286e3eb5da1069c23ec`.
- **Part 2 (S022):** `Reply.lean`, `Relocation.lean` and `Main.lean`, proof-source commit `a8bc161d2a51b92c340697af16a10e874cd9a098`. This commit contains the whole formalisation.

**Auditor:** same agent, S021 and S022. **Toolchain:** `leanprover/lean4:v4.35.0`, core only, run in a Linux cloud container with elan.
**Main declarations:**
- EC-C008(a): `EndgameChess.Rules.krk_strong_to_move_live`;
- EC-C008(b): `EndgameChess.Rules.krk_dead_iff`.

**Status:** Gate F evidence is recorded in §9–§10. EC-C008 becomes `FORMAL_VERIFIED` in S022. It is not frozen (Gate Z is S023).

# Part 1 (S021): infrastructure and end-game half

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

# Part 2 (S022): replies, relocation and main theorems

## 6. Statement correspondence (`Reply.lean`)
| Prose | Lean | Check |
|---|---|---|
| A legal non-capturing reply of the lone king | `Free sk r wk t` | Exactly `StepM.lone`'s conditions: `t` is adjacent to `L`, is not the rook's square, is not adjacent to `S`, and is not seen by the rook once `L` stands on `t`. |
| "has a non-capturing legal move, or is checkmated" | `LoneOK sk r wk` | `(∃ t, Free …) ∨ MateM …`. `MateM` is a kernel `MatedK` by `mate_sound`. |
| RL-h's exception `(S, R, L) = (c8, h7, a8)` | `HExc` (with the rook on the h-file) | Coordinates: rook rank 7, `S` = (2,7), `L` = (0,7). |
| **RL-h** | `krk_RLh` | Hypotheses: `Normal sk`, `r.1 = 7`, `r ≠ wk`, `2 ≤ dInf sk wk`, `¬HExc`. Conclusion: `LoneOK`. Each case names an explicit reply square, checked by `omega`. The case split differs from the prose's in form (details below), not in content. Every case ends in an explicit reply or in a proof of `MateM`. |
| **RL-f** | `krk_RLf` | Hypotheses: rook file `< sx`, `sx ≤ 3`, `L` off the rook's file, rank distance ≥ 2, `2 ≤ dInf sk wk`. Conclusion: a free step. `sx ≤ 3` is implicit in the prose ("`S` normalised"). It is needed: without it the reply `(x−1, y)` for `L` on the h-file could land on the rook's file. |

**RL-h case split as formalised.** Notation: `L = (x, y)`, rook `(7, ρ)`.
1. **`x = 7`:** reply `(6, y)`.
2. **`x ∈ {5, 6}`:** reply `(x, y+1)` or `(x, y−1)`, whichever is on the board and off rank `ρ`; otherwise `(11−x, y)`.
3. **`x ≤ 4`:**
   - **`|y−ρ| ≥ 2`:** reply `(x+1, y)` if `S` is ≥ 2 ranks away, otherwise `(x, y±1)`.
   - **`|y−ρ| = 1`:**
     - `(x+1, y)` if `S` is ≥ 2 ranks away;
     - otherwise the vertical square away from rank `ρ`, if it is on the board;
     - otherwise `(x±1, y)` on the side away from `S`;
     - otherwise the a8 corner: b8 if `sx ≥ 3`, a7 if `S` = c7 (shielded), and `S` = c8 is `HExc`.
   - **`y = ρ`:**
     - a vertical reply when `S` is ≥ 2 files away;
     - otherwise the vertical reply that `S` does not cover;
     - otherwise (`L` on rank 1 or 8) the inner diagonal on the side away from `S`;
     - otherwise `MateM`.

This is the prose's argument (the opposite-neighbour fact, applied case by case), with every reply made explicit.

## 7. Statement correspondence (`Relocation.lean`)
| Prose | Lean | Check |
|---|---|---|
| Facts (i)–(iii) of Lemma P1 | `RookInv sk rs wk` | The state invariant: `S` normalised, `sk ≠ rs`, kings apart, `rs ≠ wk`, the rook does not see `L`. Fact (i) is part of `step_sound` (S021). |
| (iii): after any free reply, (ii) holds again | `rookInv_of_free` | Every `Free` reply gives `RookInv`. So the route is proved from **every** state the reply can produce, as the prose requires ("any non-capturing legal move"), even though `WinM` lets us pick one. |
| (ii): `L` is not on an unshielded rook line | `shield_of_line`, `onSeg_trans`, `rook_move_ok` | A rook move whose segment and target avoid `S` also avoids `L`. |
| A rook move plus a reply | `after_rook` | `StepM.rook`, then `LoneOK`: a free reply continues from `RookInv`; a mate ends the route. |
| home | `krk_home` | Lemma S (`krk_lemmaS`, S021). |
| direct, from the h-file | `krk_hfile` | `R → h8`, a reply by RL-h (h8 ≠ h7, so the exception cannot arise), then home. |
| HV; direct, from rank 8 | `krk_rankToH` | The condition "`S` is not on the rook's rank between it and the h-file", and not the exception. `R → (h, ry)`, then RL-h, then `krk_hfile`. If the rook is on rank 8, this is the prose's "direct from rank 8" route followed by home. |
| FS (F1, F2, F3) | `krk_fs` | `R → (rx, y′)` with `y′ ≠ ry`, `y′ ≠` rank 7, `y′ ≠ sy`, and `|L_y − y′| ≥ 2`. The reply is by RL-f in F1/F3 (L is off the rook's file: `S`, to the rook's right, cannot shield it on that file), or `Ka8–a7` in F2. Then `krk_rankToH`. |
| **Lemma P1** with §3's rule | `krk_P1` | `RookInv ⇒ WinM`. The classification is exactly the prose's: FS if `S` blocks the rank or the position is `HExc`, with `y′` = rank 1 if `L` is on rank 3 or higher, else rank 8 (rank 5 if the rook is on rank 8); otherwise HV/direct/h-file/home. |

The FS legs are the prose's. One simplification: after leg 1, legs 2 and 3 are `krk_rankToH` again, because `S` is now off the rook's rank. When `y′` is rank 8, leg 2 goes straight to h8 along rank 8, as in the prose.

## 8. Statement correspondence (`Main.lean`)
| Prose | Lean | Check |
|---|---|---|
| F1 + F4 + P1 + S + W + E + M | `krk_live_of_not_check` | `IsKRK q σ sk rs wk`, `q.turn = σ`, `inCheck q σ.opp = false` ⇒ `¬DeadK q`, for any flags. A `BoardSym` from `exists_sym_normal` maps the state to `RookInv`. `krk_P1` gives `WinM` there, and `winM_of_sym` and `not_deadK_of_winM` bring it back to `q`. |
| **EC-C008(a)** | `krk_strong_to_move_live` | `Legal p q`, `IsKRK q σ sk rs wk`, `q.turn = σ` ⇒ `¬DeadK q`. F1: the mover of the last move (`σ.opp`) is not in check (`legal_mover_safe`). Both orientations (`σ` arbitrary); any flags. |
| §1 "(a) ⇒ (b)", the move of the lone king | `lone_move_cases`, `reachK_cons` | A legal lone-king move gives K+R vs K with `σ` to move, or captures the rook and gives `IsKK` (both colour cases are built explicitly). Castling is excluded (no rook of the lone side). |
| **EC-C008(b)** | `krk_dead_iff` | `IsKRK q σ sk rs wk`, `q.turn = σ.opp` ⇒ (`DeadK q ↔ ¬MatedK q ∧ ∀ r, Legal q r → ∃ w b, IsKK r w b`). "⇐" is EC-T0006's `krk_dead_of_forced_capture`. "⇒" uses (a) on the successor. **Stronger than the prose:** no hypothesis that `q` was produced by a legal move. The proof uses only the legality of the move *from* `q`. |
| Arisen form; Art. 5.2.2 | `initial_not_KRK`, `arisen_krk_strong_live`, `krk_drawn_by_rule_iff` | For an arisen K+R vs K position: `Rule5_2_2 q .draw ↔ q.turn = σ.opp ∧ ¬MatedK q ∧ every legal move captures the rook`. This is the full L1 characterisation for K+R vs K under the rule encoding. |

## 9. Non-vacuity (`decide`) and negative controls
- `rlh_exception_example`: White Kc8, Rh7, Black Ka8, Black to move. `HExc` holds; `decide` gives not in check and `legalMoves = []`; `DeadK` follows via `krk_dead_iff`. RL-h's exception is a real stalemate, so `¬HExc` cannot be dropped.
- `fsF2_example`: White Kc8, Rd7, Black Ka8, White to move (FS case F2). `decide` gives Black not in check; `¬DeadK` via `krk_live_of_not_check`.
- `krk_strong_live_example`: from White Kd4, Ra1, Black Kf6 (Black to move), Kf6–g7 is legal (`decide`) and yields `IsKRK` with White to move. `krk_strong_to_move_live` applies, so its hypotheses are jointly satisfiable by a position produced by a legal move.
- **Negative controls** (scratch file, not committed), each rejected:
  - `legalMoves rlhExcPos ≠ []` (`decide` refutes it);
  - `inCheck fsF2Pos .black = true` (`decide` refutes it);
  - `krk_RLh` applied to `(c8, h7, a8)`: the `¬HExc` obligation cannot be discharged (unsolved goal).

## 10. Checks actually run (S022)
- `lake env lean` on each new module: no errors, no warnings. `Reply.lean` takes about 2 minutes. It sets `maxHeartbeats 4000000`, an elaboration budget only, which does not change what the kernel checks.
- `lake build` (working tree): `Build completed successfully (22 jobs)`.
- `lake env lean AxiomCheck.lean`: exit 0; 161 reports (138 + 23 new). Every report is ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `ofReduceBool`. Both main declarations: `[propext, Classical.choice, Quot.sound]`.
- Forbidden-token grep (`sorry|admit|axiom|unsafe|native_decide|implemented_by|extern`) on `Rules/KRKLive/*.lean`: 0 matches.
- No frozen module was edited. Changed under `formal/`: three new modules, `EndgameChess.lean` (+3 imports), `AxiomCheck.lean` (appended).
- **Fresh GitHub clone** of `ccr-65bb49c1-g989hw` at `a8bc161d2a51b92c340697af16a10e874cd9a098` (HEAD verified), empty `.lake`:
  - `lake build`: exit 0, `Build completed successfully (22 jobs)`, 3 min 47 s. The new modules took Basic 33 s, Endgame 7.4 s, Reply 127 s, Relocation 10 s and Main 1.3 s.
  - `lake env lean AxiomCheck.lean`: exit 0, with output byte-identical to the working-tree run (161 reports: 143 × the standard three, 5 × `[propext, Quot.sound]`, 8 × `[propext]`, the rest axiom-free).
  - Forbidden-token grep on the clone: 0 matches.
- CI: not observed.

### Axiom report (S022 declarations)
```
'EndgameChess.Rules.krk_RLh' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_RLf' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.rookInv_of_free' does not depend on any axioms
'EndgameChess.Rules.onSeg_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.shield_of_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.rook_move_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.after_rook' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_home' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_hfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_rankToH' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_fs' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_P1' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_live_of_not_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_strong_to_move_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.reachK_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.lone_move_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_dead_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.initial_not_KRK' depends on axioms: [propext]
'EndgameChess.Rules.arisen_krk_strong_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_drawn_by_rule_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.rlh_exception_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.fsF2_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_strong_live_example' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 11. Correspondence summary and coercion check
- The two main statements quantify over **all** kernel positions with K+R vs K material (`IsKRK`: exactly three pieces), both colours, and any castling rights and en-passant target. They use the kernel's own `Legal`, `ReachK`, `MatedK` and `DeadK`. No surrogate move relation appears in a main statement: the KRK model is internal, and its link to the kernel is proved (`step_sound`, `mate_sound`).
- No finite test is passed off as the theorem. `decide` appears only in the concrete examples and in `Fin` bounds; all route lemmas are proved by `omega` over symbolic coordinates.

## 12. Residual assumptions
A1; the kernel encoding (human review of `docs/RULES_KERNEL.md` still open); the audit is by the same agent.
