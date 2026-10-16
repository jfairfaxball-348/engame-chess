# Audit — EC-C001 Lean formalisation fidelity (S002)

**Subject:** `formal/EndgameChess/KK.lean` (namespace `EndgameChess.KK`) against [proofs/EC-C001_KK.md](../proofs/EC-C001_KK.md) and [docs/FOUNDATIONS.md](../docs/FOUNDATIONS.md).
**Toolchain:** `leanprover/lean4:v4.34.1` (Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`), Lake 5.0.0. Core Lean only — no mathlib, no dependencies (`lake-manifest.json` has `"packages": []`).
**Auditor:** same session as the formalisation (S002). An independent second reader has not yet reviewed it.

## 1. Definition map

| Prose (proof §2 / FOUNDATIONS) | Lean | Note |
|---|---|---|
| `F`, `S = F×F`, `(0,0)` = a1 | `Square := Fin 8 × Fin 8` | the board boundary is the type: no off-board squares exist |
| `d∞` | `dInf` via `absDiff a b := (a-b)+(b-a)` on `Nat` | `absDiff` = `\|a−b\|` because one of the truncated differences is 0 |
| A1, `N(p)` "adjoining" | `Adjoining s q`: `s ≠ q` and each coordinate differs by ≤ 1 | stated by coordinates, **not** through `dInf` |
| King attack (3.1.2–3.1.3) | `kingAttacks := Adjoining` | castling never captures (prose L1); equivalence to `dInf = 1` is the **proved** theorem `attack_iff_dInf_one`, not a definition |
| colour, `c̄` | `Colour`, `Colour.opp` | |
| KK configuration `(w,b,t)` | `KKState` (`wk`, `bk`, `turn`) | `wk = bk` can be represented (junk); it is never admissible and never results from a legal step |
| `K_c(p)` | `KKState.king p c` | |
| `InCheck(c,p)` (3.9.1) | `inCheck p c := kingAttacks (p.king c.opp) (p.king c)` | the attacker is the only opposing piece, the other king |
| `Admissible` | `2 ≤ dInf p.wk p.bk` | |
| `LegalKK` (i)–(iii) | `LegalKK p q`: ∃ s, `Adjoining (K_t) s` ∧ `s ≠ K_t̄` ∧ `q = p.moveKing s` ∧ `¬ inCheck q t` | stated with the **rule** condition (3.9.2: the mover is not in check after the move) rather than the derived `d∞ ≥ 2`; `legalKK_iff_prose` proves it equals (i)–(iii) literally |
| side to move moves; turn flips (1.2) | `moveKing` matches on `p.turn`, sets the other colour to move | `moveKing_turn`, `moveKing_kings`, `turn_of_legal_step` |
| `Checkmate(c,p)` | `p.turn = c ∧ inCheck p c ∧ ¬∃ q, LegalKK p q` | |
| `Reach` (length n ≥ 0, no stopping rule) | inductive `Reach` with `refl` and `tail` | reflexive–transitive closure; no stopping rule exists in the definition |
| `Dead(p)` | `¬∃ q, Reach p q ∧ (Checkmate .white q ∨ Checkmate .black q)` | universal over every path and both colours |

## 2. Theorem map

| Prose | Lean declaration | Statement (abridged) |
|---|---|---|
| L1 | `attack_iff_dInf_one` | `kingAttacks s q ↔ dInf s q = 1` |
| L2′ | `inCheck_iff` | `inCheck p c ↔ dInf p.wk p.bk = 1` |
| L2 | `not_inCheck_of_admissible` | `Admissible p → ¬ inCheck p c` |
| L3a (Lean side) | `legalKK_iff_prose` | rule form of `LegalKK` ↔ conditions (i)–(iii) |
| L3 | `admissible_of_legal_step`, `turn_of_legal_step` | `LegalKK p q → Admissible q` (no hypothesis on `p`); turn flips |
| L0 core | `admissible_of_last_move_legal` | `(∃ p, LegalKK p q) → Admissible q` |
| L4 | `admissible_of_reach` | induction on `Reach`; the `refl` case is the zero-length path |
| L5 | `not_checkmate_of_reach` | `Admissible p → Reach p q → ¬ Checkmate c q` |
| L6 / Theorem | **`dead_of_admissible`** | `Admissible p → Dead p` |
| Theorem, arisen form (Lean scope) | `dead_of_last_move_legal` | `(∃ p, LegalKK p q) → Dead q` |
| R1 | `exists_legal_move_of_admissible` | `Admissible p → ∃ q, LegalKK p q` |
| non-vacuity | `checkmate_satisfiable`, `reach_nontrivial` | see §3 |

Proof method: `dead_of_admissible` goes through `not_checkmate_of_reach` → `admissible_of_reach` (structural induction on `Reach`) → `admissible_of_legal_step`. No `decide` over states is used in this chain. The only `decide` calls are in the two non-vacuity examples, on concrete closed propositions. No `native_decide` anywhere.

## 3. Attempted falsifications / surrogate checks

1. **Vacuous `Checkmate`.** If `Checkmate` were unsatisfiable by construction, `Dead` would hold for every state and the theorem would say nothing. *Check:* `checkmate_satisfiable` proves `Checkmate .white ⟨a1, b2, white⟩`: White Ka1, Black Kb2 (adjacent, inadmissible), White to move. White is in check; a2 and b1 are adjacent to b2, and b2 is the king (capture is excluded). **Outcome:** `Checkmate` is satisfiable. That this happens only in inadmissible states is the content of the theorem, not a defect of the definitions.
2. **Vacuous `Reach` / no moves.** If `LegalKK` were empty, `Reach` would be just `refl`. *Check:* `reach_nontrivial` (Ka1/Kc3 → Ka2/Kc3) and R1 (`exists_legal_move_of_admissible`: every admissible state has a move). **Outcome:** paths of positive length exist from every admissible state.
3. **Turn handling.** Could the wrong king move, or the turn fail to flip? `moveKing` matches on `p.turn`; `moveKing_kings` proves the mover's king lands on `s` and the other king is unchanged; `moveKing_turn` proves the flip. `Checkmate c` requires `turn = c`. **Outcome:** consistent with 1.2.
4. **`Fin 8` off-by-one.** `Fin 8` has values 0…7 exactly, and all arithmetic is done on `.val : Nat`. Truncated subtraction is used only in `absDiff`, where `(a-b)+(b-a) = |a−b|`. In R1 the constructed squares `⟨1, _⟩` and `⟨m.val - 1, _⟩` carry bound proofs checked by `omega` (the second is used only when `m.val ≠ 0`). Corner and edge behaviour comes from the type, as in the prose. **Outcome:** no off-by-one found.
5. **Attack/movement mismatch.** Movement (i) and attack both use `Adjoining`. `attack_iff_dInf_one` ties them to `dInf = 1`, which is the form the prose uses. **Outcome:** no mismatch.
6. **King capture.** `s ≠ p.king p.turn.opp` is a separate conjunct (1.4.1). It is also implied by the check condition, mirroring the prose's double exclusion. **Outcome:** excluded.
7. **`Dead` quantifier.** `Dead` is `¬∃ q, Reach p q ∧ (mate W ∨ mate B)`, i.e. ∀ paths of any length, ∀ colours. It is not a strategy statement and not "no forced mate". **Outcome:** faithful to 5.2.2 "any series of legal moves".
8. **Hidden weakening of `LegalKK`.** A smaller `LegalKK` would make `Dead` easier to prove. *Check:* `legalKK_iff_prose` shows `LegalKK` is exactly (i)–(iii) of the prose, and prose L3a shows (i)–(iii) are exactly the FIDE-legal moves. A larger relation would only make the theorem harder, and none is used. **Outcome:** no weakening.
9. **Junk states (`wk = bk`).** They are representable, but they are not admissible, never the target of a legal step (`admissible_of_legal_step`), and not covered by any theorem hypothesis. **Outcome:** harmless.
10. **Trusted base.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every declaration (§4). These are Lean's standard axioms, introduced by `omega`/`simp` automation, and they are consistent with the classical mathematics of the prose. There are no custom axioms, no `sorry`/`admit`, no `unsafe`/`implemented_by`/`extern`, and no `native_decide` (`Lean.ofReduceBool` absent).

## 4. Recorded check outputs
`lake env lean AxiomCheck.lean` (verbatim, identical for all 12 declarations listed in `formal/AxiomCheck.lean`):
```
'EndgameChess.KK.dead_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndgameChess.KK.admissible_of_last_move_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
@EndgameChess.KK.dead_of_admissible : ∀ {p : EndgameChess.KK.KKState},
  EndgameChess.KK.Admissible p → EndgameChess.KK.Dead p
```
The grep for `sorry|admit|axiom|unsafe|native_decide|implemented_by|extern` (word-bounded) over `formal/**/*.lean`, excluding `.lake`, matched nothing. Clean-checkout build: see the S002 closeout.

## 5. Residual gaps (not closed by Lean, by design)
1. **Prose bridge.** A1 and lemma L3a (the FIDE-legal moves of a KK configuration are exactly `LegalKK`) remain prose arguments, checked in Gate L. Lean does not verify the Laws of Chess.
2. **`Arisen` is wider than the Lean L0.** Prose L0 covers the last move of a real game, which may be a *capture* from a position with more material (e.g. Kxb3 removing the last other piece). Lean's `admissible_of_last_move_legal` covers only predecessors that are themselves KK configurations. The general case rests on prose L0 (3.9.2 applied to the last move, whatever the predecessor). The main theorem `dead_of_admissible` needs only `Admissible`, so this affects only the arisen corollary. Closing it formally needs a model with more material (future EC-C002/3 infrastructure).
3. **5.2.2 rule consequence** (immediate draw) is normative and stays in prose.

**Verdict:** within the stated scope, the Lean statements are faithful to the Gate L proof, and the main theorem is proved by the invariant argument. Gate F status depends on the clean-checkout build recorded in the closeout.
