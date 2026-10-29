import EndgameChess.Rules.KQK.FramedFinish

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- A knight-offset queen with the strong king outside the driven region. -/
def Shadow (sk qs wk : Square) : Prop :=
  sk.1.val+sk.2.val ≤ 4 ∧ 8 ≤ wk.1.val+wk.2.val ∧
    qs.1.val+1 = wk.1.val ∧ qs.2.val+2 = wk.2.val

def shadowPotential (wk : Square) : Nat := 21-(2*wk.1.val+wk.2.val)

theorem sum_far {s t : Square} (hs : s.1.val+s.2.val ≤ 4)
    (ht : 8 ≤ t.1.val+t.2.val) : 2 ≤ dInf s t := by
  simp only [dInf,absDiff]; omega

theorem shadow_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hs : Shadow sk qs wk) (hx : wk.1.val ≤ 6) : ∃ r, Legal q r := by
  obtain ⟨low,high,qx,qy⟩ := hs
  let t : Square := if h : wk.2.val < 7 then (wk.1,⟨wk.2.val+1,by omega⟩)
    else (⟨wk.1.val+1,by omega⟩,⟨wk.2.val-1,by omega⟩)
  have step : dInf wk t = 1 := by
    dsimp [t]; split <;> simp only [dInf,absDiff] <;> omega
  have highT : 8 ≤ t.1.val+t.2.val := by
    dsimp [t]; split <;> dsimp <;> omega
  have ne : t ≠ qs := by dsimp [t]; split <;> simp only [ne_iff_coords] <;> omega
  have notSeen : ¬ QueenSees qs t sk t := by
    dsimp [t]; split
    · apply not_sees_of_not_line <;> simp only [absDiff] <;> omega
    · apply not_sees_of_not_line <;> simp only [absDiff] <;> omega
  obtain ⟨r,hr,_,_⟩ := weak_move hq ht step ne (sum_far low highT) notSeen
  exact ⟨r,hr⟩

/-- The defender cannot move left; its coordinate sum cannot decrease.
Their weighted sum strictly increases, so copying cannot cycle. -/
theorem shadow_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hs : Shadow sk qs wk) (hx : wk.1.val ≤ 6) (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ dInf wk t = 1 ∧
      2 ≤ dInf sk t ∧ wk.1.val ≤ t.1.val ∧
      wk.1.val+wk.2.val ≤ t.1.val+t.2.val ∧
      shadowPotential t < shadowPotential wk ∧
      (t.1.val = 7 → qs.1.val = 5 ∧
        (qs.2.val+1 = t.2.val ∨ qs.2.val+3 = t.2.val)) := by
  obtain ⟨low,high,qx,qy⟩ := hs
  have safe : SafeQueen sk qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
  obtain ⟨t,hm,hr,hd,hfar,hn⟩ := safe_reply hq ht safe hl
  have bounds : qs.1.val ≤ t.1.val ∧ qs.2.val+1 ≤ t.2.val := by
    simp only [dInf,absDiff] at hd; omega
  have tx : wk.1.val ≤ t.1.val := by
    by_cases h : wk.1.val ≤ t.1.val
    · exact h
    · apply False.elim
      apply hn
      apply rook_sees_queen
      have line : RookLine qs t := ⟨by omega,Or.inl (by omega)⟩
      refine ⟨line,?_,not_onSeg_end _ _⟩
      simp only [OnSeg]; omega
  have sum : wk.1.val+wk.2.val ≤ t.1.val+t.2.val := by
    by_cases h : wk.1.val+wk.2.val ≤ t.1.val+t.2.val
    · exact h
    · exact False.elim (hn (near_sees (by simp only [dInf,absDiff]; omega)))
  have weight : 2*wk.1.val+wk.2.val < 2*t.1.val+t.2.val := by
    simp only [dInf,absDiff] at hd
    omega
  have potential : shadowPotential t < shadowPotential wk := by
    have bx := wk.1.isLt
    have by' := wk.2.isLt
    have txb := t.1.isLt
    have tyb := t.2.isLt
    simp only [shadowPotential]; omega
  refine ⟨t,hm,hr,hd,hfar,tx,sum,potential,?_⟩
  intro edge
  have five : qs.1.val = 5 := by simp only [dInf,absDiff] at hd; omega
  refine ⟨five,?_⟩
  have ys : qs.2.val+1 = t.2.val ∨ qs.2.val+2 = t.2.val ∨ qs.2.val+3 = t.2.val := by
    simp only [dInf,absDiff] at hd; omega
  rcases ys with one | two | three
  · exact Or.inl one
  · exact False.elim (hn ((sees_split).mpr (Or.inr ⟨
      by simp only [KBK.onDiag,ne_iff_coords,absDiff]; omega,
      by simp only [KBK.between,KBK.onDiag,dInf,absDiff,ne_iff_coords]; omega,
      by simp [KBK.between,KBK.onDiag]⟩)))
  · exact Or.inr three

end EndgameChess.Rules.KQK
