import EndgameChess.Rules.KQK.FarFileEntry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem same_rank_no_file {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (same : qs.2.val = sk.2.val)
    (gap : sk.2.val+2 ≤ wk.2.val) (hc : inCheck q σ.opp = false) :
    qs.1.val ≠ wk.1.val := by
  intro equal
  have different := ne_iff_coords.mp hq.1
  have see : QueenSees qs wk sk wk := by
    apply rook_sees_queen
    refine ⟨⟨ne_iff_coords.mp hq.2.2.1,Or.inl equal⟩,?_,not_onSeg_end _ _⟩
    simp only [OnSeg]; omega
  have check := (weak_check hq).mpr (Or.inr see)
  rw [hc] at check
  cases check

private theorem positive_right_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (same : qs.2.val = sk.2.val) (positive : 0 < sk.2.val)
    (gap : sk.2.val+2 ≤ wk.2.val) (right : qs.1.val < wk.1.val) :
    MateWithin σ 93 q := by
  by_cases band : OpenBand qs
  · let su : Square := (sk.1,⟨sk.2.val-1,by have bound := sk.2.isLt; omega⟩)
    obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht
      (by simp only [dInf,absDiff,su]; omega)
      (by simp only [ne_iff_coords,su]; omega)
      (by simp only [dInf,absDiff,su]; omega)
    have wall : Wall su qs wk := ⟨by dsimp [su]; omega,by omega,right⟩
    have safe : SafeQueen su qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
    exact mateWithin_choose ht hl (wall_weak_ninety_two hm hct wall band safe)
  · have qy : qs.2.val = 5 := by
      have bound := wk.2.isLt
      by_cases low : qs.2.val ≤ 4
      · exact False.elim (band (Or.inl low))
      · omega
    have qx : qs.1.val = 6 := by
      have bound := wk.1.isLt
      by_cases left : qs.1.val ≤ 5
      · exact False.elim (band (Or.inr ⟨qy,left⟩))
      · omega
    have wx : wk.1.val = 7 := by have bound := wk.1.isLt; omega
    have wy : wk.2.val = 7 := by have bound := wk.2.isLt; omega
    exact mateWithin_mono (corner_knight_low_five_rescue hq ht (by omega) qx qy wx wy) (by decide)

private theorem positive_same_rank_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (same : qs.2.val = sk.2.val) (positive : 0 < sk.2.val)
    (gap : sk.2.val+2 ≤ wk.2.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  have different := same_rank_no_file hq same gap hc
  by_cases right : qs.1.val < wk.1.val
  · exact positive_right_entry hq ht same positive gap right
  · apply unframe_bound reflectX hq
    apply positive_right_entry (framed_material reflectX hq) ht
    · dsimp [reflectX,symX]; exact same
    · dsimp [reflectX,symX]; exact positive
    · dsimp [reflectX,symX]; exact gap
    · dsimp [reflectX,symX]; omega

private theorem protected_backrank_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (ky : sk.2.val = 0) (qy : qs.2.val = 0) (wy : 2 ≤ wk.2.val)
    (adjacent : absDiff sk.1.val qs.1.val = 1) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  have different := same_rank_no_file hq (by omega) (by omega) hc
  let nq : Square := (qs.1,1)
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht
    (near_sees (by simp only [dInf,absDiff,nq]; omega))
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have safe : SafeQueen sk nq wk := Or.inr (by simp only [dInf,absDiff,nq] at adjacent ⊢; omega)
  exact mateWithin_choose ht hl (low_rank_weak_bound hm hct
    (by dsimp [nq]; omega) (by dsimp [nq]; omega)
    (by change (1 : Nat) ≤ 4; decide) different safe)

private theorem backrank_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (ky : sk.2.val = 0) (qy : qs.2.val = 0) (wy : 2 ≤ wk.2.val)
    (hc : inCheck q σ.opp = false) : MateWithin σ 97 q := by
  have distinct := ne_iff_coords.mp hq.1
  have different := same_rank_no_file hq (by omega) (by omega) hc
  by_cases files : 2 ≤ absDiff qs.1.val wk.1.val
  · exact mateWithin_mono (clear_low_wall_entry hq ht (by omega) (by omega)
      (Or.inl (by omega)) files hc) (by decide)
  by_cases horizontal : 2 ≤ absDiff sk.1.val wk.1.val
  · by_cases forward : sk.1.val+2 ≤ wk.1.val
    · apply unframe_bound swap hq
      exact offrank_entry (framed_material swap hq) ht forward
        (by dsimp [swap,symSwap]; omega) (framed_weak_not_check swap hq hc)
    · apply unframe_bound anti hq
      apply offrank_entry (framed_material anti hq) ht
      · dsimp [anti,symAnti]; simp only [absDiff] at horizontal; omega
      · dsimp [anti,symAnti]; omega
      · exact framed_weak_not_check anti hq hc
  by_cases adjacent : absDiff sk.1.val qs.1.val = 1
  · exact mateWithin_mono (protected_backrank_entry hq ht ky qy wy adjacent hc) (by decide)
  have kingStep : absDiff sk.1.val wk.1.val = 1 := by
    simp only [absDiff] at horizontal files adjacent ⊢; omega
  have queenAdjacent : absDiff wk.1.val qs.1.val = 1 := by
    simp only [absDiff] at horizontal files adjacent ⊢; omega
  let su : Square := (wk.1,sk.2)
  obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su] at kingStep ⊢; omega)
    (by simp only [ne_iff_coords,su]; omega)
    (by simp only [dInf,absDiff,su]; omega)
  have safe : SafeQueen su qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
  have hne : ∃ r, Legal c r := by
    let y : Fin 8 := ⟨if wk.2.val = 7 then 6 else wk.2.val+1,by
      have bound := wk.2.isLt; split <;> omega⟩
    have yProps : absDiff wk.2.val y.val = 1 ∧ 3 ≤ y.val := by
      have bound := wk.2.isLt
      dsimp [y]; split <;> simp only [absDiff] <;> omega
    let t : Square := (wk.1,y)
    obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
      (by simp only [dInf,absDiff,t] at yProps ⊢; omega)
      (by simp only [ne_iff_coords,t]; omega)
      (by simp only [dInf,absDiff,su,t]; omega)
      (by apply not_sees_of_not_line <;> simp only [absDiff,t] at queenAdjacent ⊢ <;> omega)
    exact ⟨r,hr⟩
  have result : MateWithin σ 95 q := by
    apply mateWithin_pair ht hl hct hne
    intro r hr
    obtain ⟨t,hmt,hrt,hd,hfar,_⟩ := safe_reply hm hct safe hr
    have upper : 2 ≤ t.2.val := by simp only [dInf,absDiff,su] at hd hfar; omega
    have notCheck := legal_mover_safe hr
    rw [hct] at notCheck
    exact protected_backrank_entry hmt hrt ky qy upper queenAdjacent notCheck
  exact mateWithin_mono result (by decide)

theorem same_rank_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val) (same : qs.2.val = sk.2.val)
    (hc : inCheck q σ.opp = false) : MateWithin σ 97 q := by
  by_cases positive : 0 < sk.2.val
  · exact mateWithin_mono (positive_same_rank_entry hq ht same positive gap hc) (by decide)
  · exact backrank_entry hq ht (by omega) (by omega) (by omega) hc

end EndgameChess.Rules.KQK
