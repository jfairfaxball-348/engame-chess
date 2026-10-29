import EndgameChess.Rules.KQK.FarFilePreparation

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- Weak-turn wall composition keeps the escape obligation explicit. -/
theorem separating_rank_weak_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (below : sk.2.val < qs.2.val) (above : qs.2.val < wk.2.val)
    (safe : SafeQueen sk qs wk) (hne : ∃ r, Legal q r) : MateWithin σ 92 q := by
  apply mateWithin_defend ht hne
  intro r hr
  obtain ⟨t,hm,hrt,upper⟩ := rank_reply hq ht safe below above hr
  have hc := legal_mover_safe hr
  rw [ht] at hc
  exact separating_rank_bound hm hrt below upper hc

/-- A corner rook-mate pattern is also a queen mate. This geometric
terminal handles the narrow setup branch without a stalemating wall move. -/
theorem corner_distant_mated {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (kx : sk.1.val = 5) (ky : sk.2.val = 6)
    (qx : qs.1.val = 7) (qy : qs.2.val = 5)
    (wx : wk.1.val = 7) (wy : wk.2.val = 7) : MatedK q := by
  constructor
  · rw [ht]
    apply (weak_check hq).mpr
    right
    apply rook_sees_queen
    refine ⟨⟨ne_iff_coords.mp hq.2.2.1,Or.inl (by omega)⟩,?_,not_onSeg_end _ _⟩
    simp only [OnSeg]; omega
  · rintro ⟨r,hr⟩
    have safe : SafeQueen sk qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
    obtain ⟨t,_,_,hd,hfar,hn⟩ := safe_reply hq ht safe hr
    have bx := t.1.isLt
    have by' := t.2.isLt
    have point : t.1.val = 7 ∧ t.2.val = 6 := by
      simp only [dInf,absDiff] at hd hfar
      omega
    exact hn (near_sees (by simp only [dInf,absDiff]; omega))

private theorem low_right_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val) (low : sk.2.val ≤ 4)
    (clear : qs.1.val ≠ sk.1.val ∨ sk.2.val < qs.2.val)
    (files : qs.1.val+2 ≤ wk.1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  by_cases already : qs.2.val = sk.2.val+1
  · exact mateWithin_mono (separating_rank_bound hq ht (by omega) (by omega) hc) (by decide)
  let nq : Square := (qs.1,⟨sk.2.val+1,by omega⟩)
  have see : QueenSees qs nq sk wk := by
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inl rfl⟩,?_,?_⟩
    · rcases clear with off | higher <;> simp only [OnSeg,nq] <;> omega
    · simp only [OnSeg,nq]; omega
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have band : OpenBand nq := by
    by_cases lower : sk.2.val ≤ 3
    · exact Or.inl (by dsimp [nq]; omega)
    · have bx := wk.1.isLt
      exact Or.inr ⟨by dsimp [nq]; omega,by dsimp [nq]; omega⟩
  have wall : Wall sk nq wk := ⟨by dsimp [nq]; omega,by dsimp [nq]; omega,by dsimp [nq]; omega⟩
  have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
  exact mateWithin_choose ht hl (wall_weak_ninety_two hm hct wall band safe)

/-- A two-file margin suffices when the new queen wall is below rank six. -/
theorem clear_low_wall_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val) (low : sk.2.val ≤ 4)
    (clear : qs.1.val ≠ sk.1.val ∨ sk.2.val < qs.2.val)
    (files : 2 ≤ absDiff qs.1.val wk.1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  by_cases right : qs.1.val+2 ≤ wk.1.val
  · exact low_right_entry hq ht gap low clear right hc
  · have hm : IsKQK (pos σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) q.turn)
        σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) :=
      ⟨reflectX.toBoardSym.ne_iff.mpr hq.1,reflectX.toBoardSym.ne_iff.mpr hq.2.1,
        reflectX.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
    apply unframe_bound reflectX hq
    apply low_right_entry hm ht
    · dsimp [reflectX,symX]; exact gap
    · dsimp [reflectX,symX]; exact low
    · rcases clear with off | higher
      · left; dsimp [reflectX,symX]; omega
      · right; dsimp [reflectX,symX]; exact higher
    · dsimp [reflectX,symX]; simp only [absDiff] at files; omega
    · exact framed_weak_not_check reflectX hq hc

end EndgameChess.Rules.KQK
