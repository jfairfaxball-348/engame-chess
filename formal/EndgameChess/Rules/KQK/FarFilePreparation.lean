import EndgameChess.Rules.KQK.ClearWallEntry

/-! Prepare a far file while preserving an explicit horizontal weak escape.
Two adjacent candidate files suffice to avoid its queen diagonal. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- Safe off-rank preparation on file zero or one. The target file is
chosen from the escape witness, rather than fixed in advance: a fixed
far file can stalemate when its diagonal removes the last reply. -/
theorem far_file_preparation {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val) (right : 4 ≤ wk.1.val)
    (offKing : qs.2.val ≠ sk.2.val) (offWeak : qs.2.val ≠ wk.2.val)
    (notFar : 2 ≤ qs.1.val) :
    ∃ c nq, Legal q c ∧ IsKQK c σ sk nq wk ∧ c.turn = σ.opp ∧
      nq.2 = qs.2 ∧ nq.1.val ≤ 1 ∧ (∃ r, Legal c r) ∧
      (∀ r, Legal c r → ∃ t, IsKQK r σ sk nq t ∧ r.turn = σ ∧
        3 ≤ t.1.val ∧ sk.2.val+1 ≤ t.2.val ∧ 2 ≤ dInf sk t ∧
        nq.2.val ≠ t.2.val ∧ inCheck r σ.opp = false) := by
  let x : Fin 8 := ⟨if wk.1.val = 7 then 6 else wk.1.val+1,by
    have bound := wk.1.isLt; split <;> omega⟩
  have xProps : absDiff wk.1.val x.val = 1 ∧ 5 ≤ x.val := by
    have bound := wk.1.isLt
    dsimp [x]; split <;> simp only [absDiff] <;> omega
  let f : Fin 8 := ⟨if x.val = absDiff qs.2.val wk.2.val then 1 else 0,by split <;> decide⟩
  have fSmall : f.val ≤ 1 := by dsimp [f]; split <;> omega
  have notDiagonal : absDiff f.val x.val ≠ absDiff qs.2.val wk.2.val := by
    dsimp [f]
    split <;> simp only [absDiff] at * <;> omega
  let nq : Square := (f,qs.2)
  have see : QueenSees qs nq sk wk := by
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inr rfl⟩,?_,?_⟩
    · simp only [OnSeg,nq]; omega
    · simp only [OnSeg,nq]; omega
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
  have hne : ∃ r, Legal c r := by
    let t : Square := (x,wk.2)
    obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
      (by simp only [dInf,absDiff,t] at xProps ⊢; omega)
      (by simp only [ne_iff_coords,t,nq]; omega)
      (by simp only [dInf,absDiff,t]; omega)
      (by
        apply not_sees_of_not_line
        · dsimp [nq,t]; omega
        · exact offWeak
        · exact notDiagonal)
    exact ⟨r,hr⟩
  refine ⟨c,nq,hl,hm,hct,rfl,fSmall,hne,?_⟩
  intro r hr
  obtain ⟨t,hmt,hrt,hd,hfar,hn⟩ := safe_reply hm hct safe hr
  have tx : 3 ≤ t.1.val := by simp only [dInf,absDiff] at hd; omega
  have ty : sk.2.val+1 ≤ t.2.val := by simp only [dInf,absDiff] at hd; omega
  have off : nq.2.val ≠ t.2.val := by
    intro equal
    apply hn
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inr equal⟩,?_,not_onSeg_end _ _⟩
    simp only [OnSeg,nq]; omega
  have hc := legal_mover_safe hr
  rw [hct] at hc
  exact ⟨t,hmt,hrt,tx,ty,hfar,off,hc⟩

end EndgameChess.Rules.KQK
