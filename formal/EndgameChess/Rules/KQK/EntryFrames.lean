import EndgameChess.Rules.KQK.SetupCorners

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def anti : QueenSym where
  toBoardSym := symAnti
  diag_iff s t := by
    simp only [KBK.onDiag,symAnti,ne_iff_coords,absDiff]; omega

theorem framed_material (g : QueenSym) {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) :
    IsKQK (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn) σ (g.f sk) (g.f qs) (g.f wk) :=
  ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
    g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩

theorem framed_safe (g : QueenSym) {sk qs wk : Square} (hs : SafeQueen sk qs wk) :
    SafeQueen (g.f sk) (g.f qs) (g.f wk) := by
  rcases hs with far | protect
  · left; simpa only [g.dInf_eq] using far
  · right; simpa only [g.dInf_eq] using protect

theorem framed_separating_rank_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (below : (g.f sk).2.val < (g.f qs).2.val)
    (above : (g.f qs).2.val < (g.f wk).2.val)
    (hc : inCheck q σ.opp = false) : MateWithin σ 91 q := by
  apply unframe_bound g hq
  exact separating_rank_bound (framed_material g hq) ht below above (framed_weak_not_check g hq hc)

/-- A protected checking source may start only one file beyond the queen.
Exclude precisely the narrow nonchecking corner trap when choosing its
horizontal escape. -/
theorem edge_wall_weak_open_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (low : sk.2.val ≤ 5) (qy : qs.2.val = 6) (wy : wk.2.val = 7)
    (gap : qs.1.val+1 ≤ wk.1.val) (safe : SafeQueen sk qs wk)
    (notTrap : qs.1.val ≤ 4 ∨ wk.1.val ≤ 6) : MateWithin σ 92 q := by
  let x : Fin 8 := ⟨if wk.1.val = 7 then 6 else wk.1.val+1,by
    have bound := wk.1.isLt; split <;> omega⟩
  have xProps : absDiff wk.1.val x.val = 1 ∧ qs.1.val+2 ≤ x.val := by
    have bound := wk.1.isLt
    dsimp [x]; split <;> simp only [absDiff]
    · rcases notTrap with left | right <;> omega
    · omega
  have hne : ∃ r, Legal q r := by
    let t : Square := (x,7)
    obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hq ht
      (by simp only [dInf,absDiff,t] at xProps ⊢; omega)
      (by simp only [ne_iff_coords,t]; omega)
      (by simp only [dInf,absDiff,t]; omega)
      (by apply not_sees_of_not_line <;> simp only [absDiff,t] <;> omega)
    exact ⟨r,hr⟩
  exact separating_rank_weak_bound hq ht (by omega) (by omega) safe hne

theorem low_rank_weak_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (below : sk.2.val < qs.2.val) (above : qs.2.val < wk.2.val)
    (low : qs.2.val ≤ 4) (different : qs.1.val ≠ wk.1.val)
    (safe : SafeQueen sk qs wk) : MateWithin σ 92 q := by
  by_cases right : qs.1.val < wk.1.val
  · exact wall_weak_ninety_two hq ht ⟨below,above,right⟩ (Or.inl low) safe
  · apply unframe_bound reflectX hq
    apply wall_weak_ninety_two (framed_material reflectX hq) ht
    · dsimp [Wall,reflectX,symX]; omega
    · left; dsimp [reflectX,symX]; exact low
    · exact framed_safe reflectX safe

theorem framed_wall_weak_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (wall : Wall (g.f sk) (g.f qs) (g.f wk))
    (band : OpenBand (g.f qs)) (safe : SafeQueen sk qs wk) : MateWithin σ 92 q := by
  apply unframe_bound g hq
  exact wall_weak_ninety_two (framed_material g hq) ht wall band (framed_safe g safe)

end EndgameChess.Rules.KQK
