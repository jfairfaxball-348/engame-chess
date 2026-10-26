import EndgameChess.Rules.KRKForcing.AxisWalls

/-! Terminal geometry supporting the open positive-clock lower-bound problem.
No outcome classification or exact global distance is claimed. -/
namespace EndgameChess.Rules.KRKMateGeometry
open EndgameChess.KK
set_option maxHeartbeats 100000

def Horizontal (sk rs wk : Square) : Prop :=
  rs.2.val = wk.2.val ∧
  ((wk.2.val = 0 ∧ sk.2.val = 2) ∨ (wk.2.val = 7 ∧ sk.2.val = 5)) ∧
  2 ≤ absDiff rs.1.val wk.1.val ∧
  (wk.1.val = 0 → sk.1.val ≤ 1) ∧
  (wk.1.val = 7 → 6 ≤ sk.1.val) ∧
  (0 < wk.1.val → wk.1.val < 7 → sk.1.val = wk.1.val)

private theorem off_rank_control {sk rs wk t : Square}
    (mate : MateM ⟨sk, rs, wk, false⟩)
    (step : dInf wk t = 1)
    (file : rs.1.val ≠ t.1.val) (rank : rs.2.val ≠ t.2.val) :
    dInf sk t ≤ 1 := by
  rcases mate.2.2 t step with h | h
  · exact h
  · exact False.elim (h.2.1.2.elim file rank)

theorem horizontal_edge {sk rs wk : Square}
    (far : 2 ≤ dInf sk wk) (rank : rs.2.val = wk.2.val)
    (mate : MateM ⟨sk, rs, wk, false⟩) :
    wk.2.val = 0 ∨ wk.2.val = 7 := by
  have file : rs.1.val ≠ wk.1.val := by
    have hline : ¬ (rs.1.val = wk.1.val ∧ rs.2.val = wk.2.val) := mate.2.1.1.1
    omega
  apply Classical.byContradiction
  intro h
  have low : 0 < wk.2.val := by omega
  have high : wk.2.val + 1 < 8 := by omega
  let up : Square := (wk.1, ⟨wk.2.val + 1, high⟩)
  let down : Square := (wk.1, ⟨wk.2.val - 1, by omega⟩)
  have hu := off_rank_control mate (t := up)
    (by simp only [up, dInf, absDiff]; omega) file (by dsimp [up]; omega)
  have hd := off_rank_control mate (t := down)
    (by simp only [down, dInf, absDiff]; omega) file (by dsimp [down]; omega)
  simp only [up, down, dInf, absDiff] at hu hd far
  omega

private theorem bottom_necessity {sk rs wk : Square}
    (far : 2 ≤ dInf sk wk) (rank : rs.2.val = wk.2.val)
    (edge : wk.2.val = 0) (mate : MateM ⟨sk, rs, wk, false⟩) :
    Horizontal sk rs wk := by
  have file : rs.1.val ≠ wk.1.val := by
    have hline : ¬ (rs.1.val = wk.1.val ∧ rs.2.val = wk.2.val) := mate.2.1.1.1
    omega
  let up : Square := (wk.1, 1)
  have hu := off_rank_control mate (t := up)
    (by simp only [up, dInf, absDiff]; omega) file (by dsimp [up]; omega)
  have kingRank : sk.2.val = 2 := by
    simp only [up, dInf, absDiff] at hu far
    omega
  have gap : 2 ≤ absDiff rs.1.val wk.1.val := by
    apply Classical.byContradiction
    intro h
    have step : dInf wk rs = 1 := by simp only [dInf, absDiff] at *; omega
    have covered := mate.2.2 rs step
    simp only [ne_eq, not_true_eq_false, false_and, or_false] at covered
    simp only [dInf, absDiff] at covered
    omega
  have left : 0 < wk.1.val → sk.1.val ≤ wk.1.val := by
    intro hx
    let t : Square := (⟨wk.1.val - 1, by omega⟩, 1)
    have ht := off_rank_control mate (t := t)
      (by simp only [t, dInf, absDiff]; omega)
      (by dsimp [t]; simp only [absDiff] at gap; omega)
      (by dsimp [t]; omega)
    simp only [t, dInf, absDiff] at ht
    omega
  have right : wk.1.val < 7 → wk.1.val ≤ sk.1.val := by
    intro hx
    let t : Square := (⟨wk.1.val + 1, by omega⟩, 1)
    have ht := off_rank_control mate (t := t)
      (by simp only [t, dInf, absDiff]; omega)
      (by dsimp [t]; simp only [absDiff] at gap; omega)
      (by dsimp [t]; omega)
    simp only [t, dInf, absDiff] at ht
    omega
  refine ⟨rank, Or.inl ⟨edge, kingRank⟩, gap, ?_, ?_, ?_⟩
  · intro hx; simp only [up, dInf, absDiff] at hu; omega
  · intro hx; simp only [up, dInf, absDiff] at hu; omega
  · intro hl hr; have := left hl; have := right hr; omega

theorem horizontal_necessity {sk rs wk : Square}
    (far : 2 ≤ dInf sk wk) (rank : rs.2.val = wk.2.val)
    (mate : MateM ⟨sk, rs, wk, false⟩) : Horizontal sk rs wk := by
  rcases horizontal_edge far rank mate with bottom | top
  · exact bottom_necessity far rank bottom mate
  · have mapped := mate_map symY mate
    have h := bottom_necessity
      (sk := symY.f sk) (rs := symY.f rs) (wk := symY.f wk)
      (by rw [symY.dInf_eq]; exact far)
      (by simp only [symY]; omega) (by simp only [symY]; omega) mapped
    simp only [Horizontal, symY, absDiff] at h ⊢
    omega

theorem horizontal_sufficiency {sk rs wk : Square}
    (h : Horizontal sk rs wk) : MateM ⟨sk, rs, wk, false⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [Horizontal, RookSees, RookLine, OnSeg, absDiff] at h ⊢
    omega
  · intro t step
    change dInf sk t ≤ 1 ∨ (t ≠ rs ∧ RookSees rs t sk t)
    by_cases rank : t.2.val = wk.2.val
    · right
      simp only [Horizontal, RookSees, RookLine, OnSeg, ne_iff_coords,
        dInf, absDiff] at h step ⊢
      omega
    · left
      simp only [Horizontal, dInf, absDiff] at h step ⊢
      omega

/-- Closed coordinate terminal formula; no search or outcome values. -/
def Terminal (sk rs wk : Square) : Prop :=
  Horizontal sk rs wk ∨ Horizontal (sk.2, sk.1) (rs.2, rs.1) (wk.2, wk.1)

theorem mate_iff_terminal {sk rs wk : Square} (far : 2 ≤ dInf sk wk) :
    MateM ⟨sk, rs, wk, false⟩ ↔ Terminal sk rs wk := by
  constructor
  · intro mate
    have line : rs.1.val = wk.1.val ∨ rs.2.val = wk.2.val := mate.2.1.1.2
    rcases line with file | rank
    · right
      exact horizontal_necessity
        (by change 2 ≤ dInf (symSwap.f sk) (symSwap.f wk); rw [symSwap.dInf_eq]; exact far)
        file (mate_map symSwap mate)
    · exact Or.inl (horizontal_necessity far rank mate)
  · intro h
    rcases h with h | h
    · exact horizontal_sufficiency h
    · exact mate_map symSwap (horizontal_sufficiency h)

/-- A legal ordinary king step cannot be the mating move from a nonchecking root. -/
theorem king_step_not_mate {sk rs wk t : Square}
    (step : dInf sk t = 1) (far : 2 ≤ dInf t wk)
    (notCheck : ¬ RookSees rs wk sk wk) : ¬MateM ⟨t, rs, wk, false⟩ := by
  intro mate
  have terminal := (mate_iff_terminal far).mp mate
  have check : RookSees rs wk t wk := mate.2.1
  apply notCheck
  refine ⟨check.1, ?_, not_onSeg_end _ _⟩
  rcases terminal with horizontal | vertical
  · obtain ⟨rank, edge, gap, _⟩ := horizontal
    simp only [OnSeg, dInf, absDiff] at step gap ⊢
    omega
  · obtain ⟨file, edge, gap, _⟩ := vertical
    dsimp only at file edge gap
    simp only [OnSeg, dInf, absDiff] at step gap ⊢
    omega

/-- Necessity uses both noncapturing moves and the actual legal rook capture. -/
theorem kernel_mate_model {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (mate : MatedK q) :
    MateM ⟨sk, rs, wk, false⟩ := by
  have check := mate.1
  rw [turn] at check
  have sees : RookSees rs wk sk wk := by
    rcases (inCheck_weak_krk material.1 material.2.1 material.2.2.1
      material.2.2.2).mp check with adjacent | sees
    · omega
    · exact sees
  refine ⟨rfl, sees, ?_⟩
  intro t step
  change dInf sk t ≤ 1 ∨ (t ≠ rs ∧ RookSees rs t sk t)
  by_cases near : dInf sk t ≤ 1
  · exact Or.inl near
  have apart : 2 ≤ dInf sk t := by omega
  by_cases capture : t = rs
  · subst t
    obtain ⟨r, legal, _⟩ := krk_unprotected_capture material turn step apart
    exact False.elim (mate.2 ⟨r, legal⟩)
  · by_cases seen : RookSees rs t sk t
    · exact Or.inr ⟨capture, seen⟩
    · obtain ⟨r, legal, _⟩ := step_sound
        (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩)
        (StepM.lone step capture apart seen)
      exact False.elim (mate.2 ⟨r, legal⟩)

/-- Exact checkmate classification in the actual kernel, for either strong
colour and arbitrary flags, under the explicit legal king-separation premise. -/
theorem kernel_mate_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) : MatedK q ↔ Terminal sk rs wk := by
  constructor
  · intro mate
    exact (mate_iff_terminal far).mp (kernel_mate_model material turn far mate)
  · intro h
    exact mate_sound (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩)
      ((mate_iff_terminal far).mpr h)

end EndgameChess.Rules.KRKMateGeometry

