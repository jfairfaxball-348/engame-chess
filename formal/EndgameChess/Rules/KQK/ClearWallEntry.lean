import EndgameChess.Rules.KQK.BandFrames

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem clear_right_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val)
    (clear : qs.1.val ≠ sk.1.val ∨ sk.2.val < qs.2.val)
    (files : qs.1.val+3 ≤ wk.1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  by_cases already : qs.2.val = sk.2.val+1
  · exact mateWithin_mono (wall_ninety_one hq ht ⟨by omega,by omega,by omega⟩ hc) (by decide)
  let nq : Square := (qs.1,⟨sk.2.val+1,by have bound := wk.2.isLt; omega⟩)
  have see : QueenSees qs nq sk wk := by
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inl rfl⟩,?_,?_⟩
    · rcases clear with off | higher <;> simp only [OnSeg,nq] <;> omega
    · simp only [OnSeg,nq]; omega
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have wall : Wall sk nq wk := ⟨by dsimp [nq]; omega,by dsimp [nq]; omega,by dsimp [nq]; omega⟩
  have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
  apply mateWithin_pair ht hl hct (wall_far_reply_exists hm hct wall files)
  intro r hr
  obtain ⟨t,hmt,hrt,next,_,_,notCheck⟩ := wall_reply hm hct wall safe hr
  exact wall_ninety_one hmt hrt next notCheck

/-- A clear vertical slide into a wall, with a file margin large enough to
retain a weak escape even in the last two ranks. -/
theorem clear_wall_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val)
    (clear : qs.1.val ≠ sk.1.val ∨ sk.2.val < qs.2.val)
    (files : 3 ≤ absDiff qs.1.val wk.1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  by_cases right : qs.1.val+3 ≤ wk.1.val
  · exact clear_right_entry hq ht gap clear right hc
  · have hm : IsKQK (pos σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) q.turn)
        σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) :=
      ⟨reflectX.toBoardSym.ne_iff.mpr hq.1,reflectX.toBoardSym.ne_iff.mpr hq.2.1,
        reflectX.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
    apply unframe_bound reflectX hq
    apply clear_right_entry hm ht
    · dsimp [reflectX,symX]; exact gap
    · rcases clear with off | higher
      · left; dsimp [reflectX,symX]; omega
      · right; dsimp [reflectX,symX]; exact higher
    · dsimp [reflectX,symX]; simp only [absDiff] at files; omega
    · exact framed_weak_not_check reflectX hq hc

end EndgameChess.Rules.KQK
