import EndgameChess.Rules.KQK.OrientedEntry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem tight_king_step {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (farFile : qs.1.val ≤ 1) (right : 3 ≤ wk.1.val)
    (qy : sk.2.val+2 = qs.2.val) (wy : sk.2.val+1 = wk.2.val)
    (gap : 2 ≤ absDiff sk.1.val wk.1.val) :
    ∃ c, Legal q c ∧ IsKQK c σ (sk.1,wk.2) qs wk ∧ c.turn = σ.opp ∧
      (∃ r, Legal c r) ∧
      (∀ r, Legal c r → ∃ t, IsKQK r σ (sk.1,wk.2) qs t ∧ r.turn = σ ∧
        2 ≤ t.1.val ∧ 2 ≤ absDiff sk.1.val t.1.val ∧
        t.2.val ≤ wk.2.val ∧ wk.2.val ≤ t.2.val+1) := by
  let su : Square := (sk.1,wk.2)
  obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; omega)
    (by simp only [dInf,su]; omega)
  have safe : SafeQueen su qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
  have hne : ∃ r, Legal c r := by
    by_cases forward : sk.1.val+2 ≤ wk.1.val
    · by_cases edge : wk.1.val = 7
      · let t : Square := (wk.1,⟨wk.2.val-1,by have bound := wk.2.isLt; omega⟩)
        obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
          (by simp only [dInf,absDiff,t]; omega)
          (by simp only [ne_iff_coords,t]; omega)
          (by simp only [dInf,absDiff,su,t]; omega)
          (by apply not_sees_of_not_line <;> simp only [absDiff,t] <;> omega)
        exact ⟨r,hr⟩
      · let t : Square := (⟨wk.1.val+1,by have bound := wk.1.isLt; omega⟩,wk.2)
        obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
          (by simp only [dInf,absDiff,t]; omega)
          (by simp only [ne_iff_coords,t]; omega)
          (by simp only [dInf,absDiff,su,t]; omega)
          (by apply not_sees_of_not_line <;> simp only [absDiff,t] <;> omega)
        exact ⟨r,hr⟩
    · have backward : wk.1.val+2 ≤ sk.1.val := by simp only [absDiff] at gap; omega
      let y : Fin 8 := ⟨if wk.1.val = qs.1.val+2 then wk.2.val-1 else wk.2.val,by
        have bound := wk.2.isLt; split <;> omega⟩
      let t : Square := (⟨wk.1.val-1,by have bound := wk.1.isLt; omega⟩,y)
      have yProps : absDiff wk.2.val y.val ≤ 1 ∧ y.val < qs.2.val := by
        dsimp [y]; split <;> simp only [absDiff] <;> omega
      obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
        (by simp only [dInf,absDiff,t] at yProps ⊢; omega)
        (by simp only [ne_iff_coords,t]; omega)
        (by simp only [dInf,absDiff,su,t]; omega)
        (by
          apply not_sees_of_not_line
          · dsimp [t]; omega
          · dsimp [t]; omega
          · dsimp [t,y]; split <;> simp only [absDiff] <;> omega)
      exact ⟨r,hr⟩
  refine ⟨c,hl,hm,hct,hne,?_⟩
  intro r hr
  obtain ⟨t,hmt,hrt,hd,hfar,hn⟩ := safe_reply hm hct safe hr
  have tx : 2 ≤ t.1.val := by simp only [dInf,absDiff] at hd; omega
  have horizontal : 2 ≤ absDiff sk.1.val t.1.val := by
    simp only [dInf,absDiff,su] at hd hfar ⊢
    omega
  have upper : t.2.val ≤ wk.2.val := by
    by_cases enough : t.2.val ≤ wk.2.val
    · exact enough
    · have equal : t.2.val = qs.2.val := by simp only [dInf,absDiff] at hd; omega
      apply False.elim
      apply hn
      apply rook_sees_queen
      refine ⟨⟨by omega,Or.inr equal.symm⟩,?_,not_onSeg_end _ _⟩
      simp only [OnSeg,su]; omega
  have lower : wk.2.val ≤ t.2.val+1 := by simp only [dInf,absDiff] at hd; omega
  exact ⟨t,hmt,hrt,tx,horizontal,upper,lower⟩

private theorem protected_file_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (farFile : qs.1.val ≤ 1) (leftClear : qs.1.val ≠ sk.1.val+1) (wx : 2 ≤ wk.1.val)
    (rank : sk.2.val+1 = qs.2.val) (height : 2 ≤ qs.2.val)
    (upper : wk.2.val ≤ sk.2.val) (lower : sk.2.val ≤ wk.2.val+1)
    (gap : 2 ≤ absDiff sk.1.val wk.1.val) : MateWithin σ 93 q := by
  by_cases corner : sk.1.val = 5 ∧ sk.2.val = 1 ∧ wk.1.val = 7 ∧ wk.2.val = 0
  · let nq : Square := (7,2)
    have see : QueenSees qs nq sk wk := by
      apply rook_sees_queen
      refine ⟨⟨by dsimp [nq]; omega,Or.inr (by dsimp [nq]; omega)⟩,?_,?_⟩
      · simp only [OnSeg,nq]; omega
      · simp only [OnSeg,nq]; omega
    obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [dInf,absDiff]; omega)
    have win : MateWithin σ 0 c := by
      apply unframe_bound reflectY hm
      exact ⟨hct,corner_distant_mated (framed_material reflectY hm) hct
        (by dsimp [reflectY,symY]; omega) (by dsimp [reflectY,symY]; omega)
        rfl rfl (by dsimp [reflectY,symY]; omega) (by dsimp [reflectY,symY]; omega)⟩
    exact mateWithin_mono (mateWithin_choose ht hl win) (by decide)
  by_cases forward : sk.1.val+2 ≤ wk.1.val
  · let nq : Square := (⟨sk.1.val+1,by have bound := wk.1.isLt; omega⟩,qs.2)
    have see : QueenSees qs nq sk wk := by
      apply rook_sees_queen
      refine ⟨⟨by dsimp [nq]; omega,Or.inr rfl⟩,?_,?_⟩
      · simp only [OnSeg,nq]; omega
      · simp only [OnSeg,nq]; omega
    obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [dInf,absDiff]; omega)
    have safe : SafeQueen sk nq wk := Or.inr (by simp only [dInf,absDiff,nq]; omega)
    have win : MateWithin σ 92 c := by
      apply unframe_bound swap hm
      apply unframe_bound reflectX (framed_material swap hm)
      have hm2 := framed_material reflectX (framed_material swap hm)
      have safe2 := framed_safe reflectX (framed_safe swap safe)
      by_cases low : sk.1.val ≤ 4
      · apply wall_weak_ninety_two hm2 hct
        · dsimp [Wall,reflectX,swap,symX,symSwap,nq]; omega
        · by_cases lowerFile : sk.1.val ≤ 3
          · left; dsimp [reflectX,swap,symX,symSwap,nq]; omega
          · right; dsimp [reflectX,swap,symX,symSwap,nq]; omega
        · exact safe2
      · have bound := wk.1.isLt
        have five : sk.1.val = 5 := by omega
        have seven : wk.1.val = 7 := by omega
        apply edge_wall_weak_open_bound hm2 hct
        · dsimp [reflectX,swap,symX,symSwap]; omega
        · dsimp [reflectX,swap,symX,symSwap,nq]; omega
        · dsimp [reflectX,swap,symX,symSwap]; omega
        · dsimp [reflectX,swap,symX,symSwap,nq]; omega
        · exact safe2
        · dsimp [reflectX,swap,symX,symSwap,nq]
          omega
    exact mateWithin_choose ht hl win
  · have backward : wk.1.val+2 ≤ sk.1.val := by simp only [absDiff] at gap; omega
    let nq : Square := (⟨sk.1.val-1,by have bound := sk.1.isLt; omega⟩,qs.2)
    have see : QueenSees qs nq sk wk := by
      apply rook_sees_queen
      refine ⟨⟨by dsimp [nq]; omega,Or.inr rfl⟩,?_,?_⟩
      · simp only [OnSeg,nq]; omega
      · simp only [OnSeg,nq]; omega
    obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [dInf,absDiff]; omega)
    have safe : SafeQueen sk nq wk := Or.inr (by simp only [dInf,absDiff,nq]; omega)
    apply mateWithin_choose ht hl
    apply framed_wall_weak_bound anti hm hct
    · dsimp [Wall,anti,symAnti,nq]; omega
    · left; dsimp [anti,symAnti,nq]; omega
    · exact safe

/-- The remaining tight above-queen geometry uses one king approach,
which makes the subsequent file wall protected. -/
theorem tight_above_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (farFile : qs.1.val ≤ 1) (right : 3 ≤ wk.1.val)
    (qy : sk.2.val+2 = qs.2.val) (wy : sk.2.val+1 = wk.2.val)
    (gap : 2 ≤ absDiff sk.1.val wk.1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 95 q := by
  by_cases already : qs.1.val = sk.1.val+1
  · exact mateWithin_mono (framed_separating_rank_bound swap hq ht
      (by dsimp [swap,symSwap]; omega) (by dsimp [swap,symSwap]; omega) hc) (by decide)
  obtain ⟨c,hl,hm,hct,hne,all⟩ := tight_king_step hq ht farFile right qy wy gap
  apply mateWithin_pair ht hl hct hne
  intro r hr
  obtain ⟨t,hmt,hrt,tx,hgap,upper,lower⟩ := all r hr
  apply protected_file_entry hmt hrt farFile
  · exact already
  · exact tx
  · change wk.2.val+1 = qs.2.val; omega
  · omega
  · exact upper
  · exact lower
  · exact hgap

end EndgameChess.Rules.KQK
