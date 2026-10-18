# Audit — EC-C007 Lean formalisation over the rules kernel (S015)

**Subject:** `formal/EndgameChess/Rules/KRK.lean`, proof-source commit `570dfa73685ea0cc98a4ab4eaf01b5f0a1edabc4`. **Prose:** [proofs/EC-C007_KRK_DEAD.md](../proofs/EC-C007_KRK_DEAD.md).
**Auditor:** same session (S015). **Toolchain:** `leanprover/lean4:v4.34.1`, core only, run locally (Windows, elan).

## 1. Statement correspondence
| Prose | Lean | Check |
|---|---|---|
| `IsKRK` (3 distinct squares, exactly σ K + σ R + σ̄ K; turn and flags free) | `krkBoard`, `IsKRK` | Same shape as the frozen `IsKNK`, with `.rook`. |
| Head decomposition of `ReachK` | `reachK_head` | Induction on the tail-inductive `ReachK`. |
| D1 | `dead_of_succ_dead` | Material-agnostic; the length-0 path is excluded by `¬MatedK q`. |
| D2 | `dead_of_succ_KK` | Each successor is reached by a legal move from `q`, so the frozen `dead_of_legal_into_KK` (EC-T0003) applies. |
| EC-C007 | `krk_dead_of_forced_capture` | Hypotheses `IsKRK`, `q.turn = σ.opp`, `¬MatedK q`, `∀ r, Legal q r → ∃ w b, IsKK r w b`. The first two are kept for the reading of the statement and are unused by the proof (named `_hk`, `_ht`). So the Lean theorem is **stronger** than the prose: it holds for any material. Both orientations, any flags. |
| 5.2.2 corollary | `krk_forced_capture_drawn_by_rule` | Adds `Arisen q`; conclusion `Rule5_2_2 q .draw`. |

## 2. Non-vacuity (`decide`)
- `krk_forced_capture_example`: from White Kh8, Rb3, Black Ka1 (White to move), **Rb3–b2 is legal**. The result is `IsKRK` with Black to move, Black is not in check, `legalMoves = [Kxb2]`, and Kxb2 yields `IsKK`. The position is proved `DeadK` **through the main theorem**, so its hypotheses are jointly satisfiable by a position produced by a legal move.
- `krk_stalemate_dead_example`: Black Ka1, White Rb2 + Kc3, Black to move: not in check, `legalMoves = []`, `DeadK` (the vacuous case).
- `krk_live_example`: White Kh6, Ra1, Black Kh8, White to move: Ra1–a8 is legal and the result is `MatedK`, so `¬DeadK`. The theorem is not a statement about all K+R vs K positions.
- **Negative control:** two deliberately false `decide` claims (`legalMoves krkStale = [kxb2]`, `legalMoves krkLive = []`) were run in a scratch file and **both rejected** (2 errors). This confirms that `decide` evaluates the kernel generator and does not pass vacuously.
- `krk_live_example` uses `set_option maxRecDepth 8192 in` (an elaborator recursion limit). It does not affect what the kernel checks or the axioms.

## 3. Checks actually run (local)
- `lake env lean EndgameChess/Rules/KRK.lean`: no errors, no warnings.
- `lake build` (working tree): `Build completed successfully (17 jobs)`.
- **Fresh clone from GitHub** at `570dfa73685ea0cc98a4ab4eaf01b5f0a1edabc4`, empty `.lake`: `lake build` exit 0 (17 jobs); `lake env lean AxiomCheck.lean` exit 0; 101 reports, all ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx`/`ofReduceBool`.
- Forbidden-token grep on `KRK.lean`: none. Under `formal/`, only `Rules/KRK.lean` (new), `EndgameChess.lean` (+1 import) and `AxiomCheck.lean` (appended) changed.
- CI: not observed.

### Clean-clone build log
```
✔ [2/17] Built EndgameChess.KK (2.2s)
✔ [3/17] Built EndgameChess.Rules.Board (858ms)
✔ [4/17] Built EndgameChess.Rules.Position (864ms)
✔ [5/17] Built EndgameChess.Rules.Moves (937ms)
✔ [6/17] Built EndgameChess.Rules.Lemmas (1.2s)
✔ [7/17] Built EndgameChess.Rules.AgreeKK (1.3s)
✔ [8/17] Built EndgameChess.KBK (10s)
✔ [9/17] Built EndgameChess.Rules.Sanity (16s)
✔ [10/17] Built EndgameChess.Rules.AgreeKBK (9.9s)
✔ [11/17] Built EndgameChess.Rules.Flags (888ms)
✔ [12/17] Built EndgameChess.Rules.Reach (912ms)
✔ [13/17] Built EndgameChess.Rules.Outcome (644ms)
✔ [14/17] Built EndgameChess.Rules.KNK (8.2s)
✔ [15/17] Built EndgameChess.Rules.KRK (3.0s)
✔ [16/17] Built EndgameChess (628ms)
Build completed successfully (17 jobs).
```

### Axiom report (EC-C007 declarations, clean clone)
```
'EndgameChess.Rules.reachK_head' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.dead_of_succ_dead' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.dead_of_succ_KK' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_dead_of_forced_capture' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_forced_capture_drawn_by_rule' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.legal_of_legalMoves_eq' depends on axioms: [propext, Quot.sound]
'EndgameChess.Rules.krk_forced_capture_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_stalemate_dead_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.Rules.krk_live_example' depends on axioms: [propext, Quot.sound]
```

## 4. Trust boundary
A1; the kernel encoding (`docs/RULES_KERNEL.md`, human review open); the 5.2.2 reading in `Rule5_2_2`; the trusted base. **No gap found.** Verdict: Gate F passes (same-session caveat).
