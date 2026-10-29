import EndgameChess.Rules.KQK.TightEntry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- Complete entry from the far-file preparation region. -/
theorem far_file_stage_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (farFile : qs.1.val ≤ 1) (right : 3 ≤ wk.1.val)
    (upper : sk.2.val+1 ≤ wk.2.val) (far : 2 ≤ dInf sk wk)
    (offKing : qs.2.val ≠ sk.2.val) (offWeak : qs.2.val ≠ wk.2.val)
    (hc : inCheck q σ.opp = false) : MateWithin σ 95 q := by
  by_cases wall : sk.2.val < qs.2.val ∧ qs.2.val < wk.2.val
  · exact mateWithin_mono (separating_rank_bound hq ht wall.1 wall.2 hc) (by decide)
  by_cases direct : sk.2.val+2 ≤ wk.2.val ∧
      (qs.1.val ≠ sk.1.val ∨ sk.2.val < qs.2.val)
  · exact mateWithin_mono (small_file_wall_entry hq ht direct.1 direct.2
      (by omega) (by omega) hc) (by decide)
  have horizontal : 2 ≤ absDiff sk.1.val wk.1.val := by
    by_cases vertical : sk.2.val+2 ≤ wk.2.val
    · have equal : qs.1.val = sk.1.val := by omega
      simp only [absDiff]; omega
    · have dy : absDiff sk.2.val wk.2.val = 1 := by simp only [absDiff]; omega
      simp only [dInf,dy] at far
      omega
  by_cases files : 2 ≤ absDiff qs.2.val wk.2.val
  · exact mateWithin_mono (horizontal_far_wall_entry hq ht upper right horizontal offKing files hc)
      (by decide)
  have qy : sk.2.val+2 = qs.2.val := by simp only [absDiff] at files; omega
  have wy : sk.2.val+1 = wk.2.val := by simp only [absDiff] at files; omega
  exact tight_above_entry hq ht farFile right qy wy horizontal hc

private theorem right_offrank_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val) (right : 4 ≤ wk.1.val)
    (off : qs.2.val ≠ sk.2.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 97 q := by
  have offWeak : qs.2.val ≠ wk.2.val := by
    intro equal
    have see : QueenSees qs wk sk wk := by
      apply rook_sees_queen
      refine ⟨⟨ne_iff_coords.mp hq.2.2.1,Or.inr equal⟩,?_,not_onSeg_end _ _⟩
      simp only [OnSeg]; omega
    have check := (weak_check hq).mpr (Or.inr see)
    rw [hc] at check
    cases check
  by_cases farFile : qs.1.val ≤ 1
  · exact mateWithin_mono (far_file_stage_bound hq ht farFile (by omega) (by omega)
      (by simp only [dInf,absDiff]; omega) off offWeak hc) (by decide)
  obtain ⟨c,nq,hl,hm,hct,qy,small,hne,all⟩ := far_file_preparation hq ht gap right off offWeak (by omega)
  apply mateWithin_pair ht hl hct hne
  intro r hr
  obtain ⟨t,hmt,hrt,right,upper,far,offt,notCheck⟩ := all r hr
  exact far_file_stage_bound hmt hrt small right upper far (by rw [qy]; exact off) offt notCheck

/-- Universal off-rank entry with a positive king rank gap. The preparation
chooses an escape-preserving far file, including all blocked/one-rank replies. -/
theorem offrank_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val) (off : qs.2.val ≠ sk.2.val)
    (hc : inCheck q σ.opp = false) : MateWithin σ 97 q := by
  by_cases right : 4 ≤ wk.1.val
  · exact right_offrank_entry hq ht gap right off hc
  · apply unframe_bound reflectX hq
    apply right_offrank_entry (framed_material reflectX hq) ht
    · dsimp [reflectX,symX]; exact gap
    · dsimp [reflectX,symX]; omega
    · dsimp [reflectX,symX]; exact off
    · exact framed_weak_not_check reflectX hq hc

end EndgameChess.Rules.KQK
