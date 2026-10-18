import EndgameChess.Rules.KRKLive.Endgame

/-!
# EC-C008 replies — Lemmas RL-h and RL-f (S022)

Formalisation of §4b (RL-h, RL-f) of `proofs/EC-C008_KRK_LIVE.md` in the KRK move model of
`Rules.KRKLive.Basic`. Both lemmas are schemas over arbitrary squares: in each case of the
prose argument an explicit reply square is given and checked by linear arithmetic on the
coordinates. Nothing is enumerated.

- `Free sk r wk t`: the lone king on `wk` may step to `t` (the conditions of `StepM.lone`);
- `LoneOK sk r wk`: a free step exists, or the position is a model mate (`MateM`);
- `HExc`: the configuration `S = c8`, rook on rank 7, `L = a8`;
- `krk_RLh`: rook on the h-file ⇒ `LoneOK`, except `HExc` (a stalemate);
- `krk_RLf`: rook on a file left of `S`, `L` off its file and ≥ 2 ranks away ⇒ a free step.

The case split of RL-h is reorganised slightly against the prose (it first splits on
whether `S` is ≥ 2 files or ≥ 2 ranks away from `L`, which makes the reply explicit), and
RL-f's proof is shorter than the prose's for the same reason. The statements are the
prose's.
-/

namespace EndgameChess.Rules

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open EndgameChess.KK

/-- The lone king on `wk` may step to `t`: adjacent, not the rook's square, not adjacent
to `S`, and not seen by the rook once it stands there. -/
def Free (sk r wk t : Square) : Prop :=
  dInf wk t = 1 ∧ t ≠ r ∧ 2 ≤ dInf sk t ∧ ¬ RookSees r t sk t

/-- After a rook move to `r`, the lone king has a free step, or it is mated. -/
def LoneOK (sk r wk : Square) : Prop :=
  (∃ t, Free sk r wk t) ∨ MateM ⟨sk, r, wk, false⟩

/-- The configuration `S = c8`, rook on rank 7, `L = a8` (RL-h's exception when the rook
is on h7). -/
def HExc (sk r wk : Square) : Prop :=
  r.2.val = 6 ∧ sk.1.val = 2 ∧ sk.2.val = 7 ∧ wk.1.val = 0 ∧ wk.2.val = 7

/-- Unfold the coordinate predicates in the goal and decide by linear arithmetic. -/
macro "geoG" : tactic =>
  `(tactic| ((try simp only [Free, MateM, RookSees, RookLine, OnSeg, ne_iff_coords, dInf,
      absDiff, true_and, and_true, true_or, or_true]) <;> omega))

theorem loneOK_of_free {sk r wk t : Square} (h : Free sk r wk t) : LoneOK sk r wk :=
  Or.inl ⟨t, h⟩

/-- **Lemma RL-h.** `S` normalised, the rook on the h-file, `L` on another square and not
adjacent to `S`, the lone king to move: it has a free step or is mated, except in the
stalemate `(S, R, L) = (c8, h7, a8)` (`HExc`). The reply is chosen explicitly in each case,
following the case split of the prose. -/
theorem krk_RLh {sk r wk : Square} (hn : Normal sk) (hr : r.1.val = 7) (hrw : r ≠ wk)
    (hfar : 2 ≤ dInf sk wk) (hx : ¬ HExc sk r wk) : LoneOK sk r wk := by
  obtain ⟨⟨sx, hsx⟩, ⟨sy, hsy⟩⟩ := sk
  obtain ⟨⟨rx, hrx⟩, ⟨ρ, hρ⟩⟩ := r
  obtain ⟨⟨x, hx8⟩, ⟨y, hy8⟩⟩ := wk
  simp only [Normal, HExc, ne_iff_coords, dInf, absDiff] at hn hr hrw hfar hx
  subst hr
  have hf : sx + 2 ≤ x ∨ x + 2 ≤ sx ∨ sy + 2 ≤ y ∨ y + 2 ≤ sy := by omega
  have hyr : x = 7 → y ≠ ρ := by omega
  obtain ⟨hn1, hn2⟩ := hn
  clear hfar hrw
  by_cases h7 : x = 7
  · -- 1. `L` on the h-file: step to the g-file
    exact loneOK_of_free (t := (⟨6, by omega⟩, ⟨y, hy8⟩)) (by clear hx; geoG)
  by_cases h56 : 5 ≤ x
  · -- 2. `L` on files f–g: a vertical step off rank `ρ`, else the horizontal one
    by_cases hu : y ≤ 6 ∧ y + 1 ≠ ρ
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y + 1, by omega⟩)) (by clear hx; geoG)
    by_cases hd : 1 ≤ y ∧ y - 1 ≠ ρ
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y - 1, by omega⟩)) (by clear hx; geoG)
    exact loneOK_of_free (t := (⟨11 - x, by omega⟩, ⟨y, hy8⟩)) (by clear hx; geoG)
  -- 3. `L` on files a–e: the rook can only see `L`'s neighbours on rank `ρ`
  by_cases hfarρ : y + 2 ≤ ρ ∨ ρ + 2 ≤ y
  · -- `|L_y − ρ| ≥ 2`: only `S` covers; step along `L`'s rank or file away from `S`
    by_cases hsr : sy + 2 ≤ y ∨ y + 2 ≤ sy
    · exact loneOK_of_free (t := (⟨x + 1, by omega⟩, ⟨y, hy8⟩)) (by clear hx; geoG)
    by_cases hy6 : y ≤ 6
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y + 1, by omega⟩)) (by clear hx; geoG)
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y - 1, by omega⟩)) (by clear hx; geoG)
  by_cases hne : y ≠ ρ
  · -- `|L_y − ρ| = 1`
    by_cases hsr : sy + 2 ≤ y ∨ y + 2 ≤ sy
    · exact loneOK_of_free (t := (⟨x + 1, by omega⟩, ⟨y, hy8⟩)) (by clear hx; geoG)
    by_cases hup : y = ρ + 1 ∧ y ≤ 6
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y + 1, by omega⟩)) (by clear hx; geoG)
    by_cases hdn : y + 1 = ρ ∧ 1 ≤ y
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y - 1, by omega⟩)) (by clear hx; geoG)
    by_cases hl : sx + 2 ≤ x
    · exact loneOK_of_free (t := (⟨x + 1, by omega⟩, ⟨y, hy8⟩)) (by clear hx; geoG)
    by_cases hx1 : 1 ≤ x
    · exact loneOK_of_free (t := (⟨x - 1, by omega⟩, ⟨y, hy8⟩)) (by clear hx; geoG)
    -- the corner a8 with the rook on h7 (the corner a1 is excluded by `sy ≥ 2`)
    by_cases hs3 : 3 ≤ sx
    · exact loneOK_of_free (t := (⟨1, by omega⟩, ⟨7, by omega⟩)) (by clear hx; geoG)
    by_cases hs6 : sy = 6
    · -- `S = c7` shields a7 on rank 7
      exact loneOK_of_free (t := (⟨0, by omega⟩, ⟨6, by omega⟩)) (by clear hx; geoG)
    -- `S = c8`: the exception
    exfalso; omega
  · -- `L` on the rook's rank
    by_cases hc : sx + 2 ≤ x ∨ x + 2 ≤ sx
    · by_cases hy6 : y ≤ 6
      · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y + 1, by omega⟩)) (by clear hx; geoG)
      · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y - 1, by omega⟩)) (by clear hx; geoG)
    by_cases hu : y ≤ 6 ∧ (sy + 1 ≤ y ∨ y + 3 ≤ sy)
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y + 1, by omega⟩)) (by clear hx; geoG)
    by_cases hd : 1 ≤ y ∧ (sy + 3 ≤ y ∨ y + 1 ≤ sy)
    · exact loneOK_of_free (t := (⟨x, hx8⟩, ⟨y - 1, by omega⟩)) (by clear hx; geoG)
    -- `L` on rank 1 or 8, the inner vertical neighbour covered by `S`
    by_cases hr1 : sx + 1 = x
    · by_cases hy0 : y = 0
      · exact loneOK_of_free (t := (⟨x + 1, by omega⟩, ⟨1, by omega⟩)) (by clear hx; geoG)
      · exact loneOK_of_free (t := (⟨x + 1, by omega⟩, ⟨6, by omega⟩)) (by clear hx; geoG)
    by_cases hr2 : sx = x + 1 ∧ 1 ≤ x
    · by_cases hy0 : y = 0
      · exact loneOK_of_free (t := (⟨x - 1, by omega⟩, ⟨1, by omega⟩)) (by clear hx; geoG)
      · exact loneOK_of_free (t := (⟨x - 1, by omega⟩, ⟨6, by omega⟩)) (by clear hx; geoG)
    -- checkmate: `S` covers the whole inner row, the rook the outer one
    clear hx
    refine Or.inr ⟨rfl, ?_, ?_⟩ <;> geoG


/-- **Lemma RL-f.** The rook on a file left of `S`, `L` off the rook's file and at rank
distance ≥ 2 from the rook, not adjacent to `S` (on files a–d): the lone king has a free
step. -/
theorem krk_RLf {sk r wk : Square} (hs3 : sk.1.val ≤ 3) (hlt : r.1.val < sk.1.val)
    (hf : wk.1.val ≠ r.1.val)
    (hy : wk.2.val + 2 ≤ r.2.val ∨ r.2.val + 2 ≤ wk.2.val) (hfar : 2 ≤ dInf sk wk) :
    ∃ t, Free sk r wk t := by
  obtain ⟨⟨sx, hsx⟩, ⟨sy, hsy⟩⟩ := sk
  obtain ⟨⟨rx, hrx⟩, ⟨ry, hry⟩⟩ := r
  obtain ⟨⟨x, hx8⟩, ⟨y, hy8⟩⟩ := wk
  simp only [dInf, absDiff] at hs3 hlt hf hy hfar
  by_cases hc : sx + 2 ≤ x ∨ x + 2 ≤ sx
  · by_cases hy6 : y ≤ 6
    · exact ⟨(⟨x, hx8⟩, ⟨y + 1, by omega⟩), by geoG⟩
    · exact ⟨(⟨x, hx8⟩, ⟨y - 1, by omega⟩), by geoG⟩
  by_cases hr : x ≤ 6 ∧ x + 1 ≠ rx
  · exact ⟨(⟨x + 1, by omega⟩, ⟨y, hy8⟩), by geoG⟩
  · exact ⟨(⟨x - 1, by omega⟩, ⟨y, hy8⟩), by geoG⟩

end EndgameChess.Rules
