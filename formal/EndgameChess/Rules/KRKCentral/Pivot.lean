import EndgameChess.Rules.KRKCentral.Guarded
import EndgameChess.Rules.KRKBox.Region

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

private theorem pivot_right {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val) (hwy : wk.2.val=rs.2.val+1)
    (hs : sk.1.val=3 ∨ sk.1.val=4) (hx : sk.1.val+2≤wk.1.val) :
    MateWithin σ 57 q := by
  let nr : Square := (⟨sk.1.val+1,by omega⟩,rs.2)
  have hnrx : nr.1.val=sk.1.val+1 := rfl
  have hnry : nr.2=rs.2 := rfl
  by_cases he : nr=rs
  · exact mateWithin_mono (guarded_bound hq (by rw [←he])
      hsy (by rw [←he]; change sk.1.val+1<wk.1.val; omega) (by omega)
      (by rw [←he]; change 3≤sk.1.val+1; omega)
      (by rw [←he]; change sk.1.val+1≤5; omega))
      (by rw [←he]; change 18*(7-(sk.1.val+1))+1≤57; omega)
  have hnrne : rs.1.val≠sk.1.val+1 := by
    intro hh
    apply he
    apply Prod.ext
    · apply Fin.ext; change sk.1.val+1=rs.1.val; omega
    · rfl
  have hs2 : StepM ⟨sk,rs,wk,true⟩ ⟨sk,nr,wk,false⟩ := by
    refine StepM.rook ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [nr,RookLine,OnSeg,ne_iff_coords,dInf,absDiff,and_true,or_true] at * <;> omega
  obtain ⟨c,hl,hm⟩ := step_sound hq hs2
  obtain ⟨t,ht⟩ := krk_box_reply_exists (sk := sk) (rs := nr) (wk := wk)
    (lo := nr.1.val+1) (hi := 7) (by change sk.2.val+1=rs.2.val; exact hsy)
    (by change rs.2.val<wk.2.val; omega) (by omega) (by omega)
    (Or.inl (by omega)) (by omega) (by omega)
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  apply mateWithin_mono (n := 55+2) ?_ (by omega)
  apply mateWithin_pair (σ := σ) hq.2 hl hm.2 ⟨v,hv⟩
  intro z hz
  obtain ⟨t,hmt,hty,hunit,hxt⟩ := krk_box_reply_region hm
    (by change sk.2.val+1=rs.2.val; exact hsy) (by change rs.2.val<wk.2.val; omega)
    (by simp only [nr,dInf,absDiff]; omega) hz
  have hwxt : nr.1.val<t.1.val := by simp only [absDiff] at hunit; omega
  exact mateWithin_mono (guarded_bound hmt (by omega) (by exact hsy) hwxt hty
    (by omega) (by omega)) (by omega)

/-- A wide lower-band central state makes one protected perpendicular cut
and finishes through a width2/3 guarded continuation. Both file directions
use actual same-budget transport; an already present cut costs no null move. -/
theorem pivot_bound {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val) (hwy : wk.2.val=rs.2.val+1)
    (hs : sk.1.val=3 ∨ sk.1.val=4) (hx : 2≤absDiff sk.1.val wk.1.val) :
    MateWithin σ 57 q := by
  by_cases hright : sk.1.val<wk.1.val
  · exact pivot_right hq hsy hwy hs (by simp only [absDiff] at hx; omega)
  have hcanon : Matches (krkPos σ (symX.f sk) (symX.f rs) (symX.f wk) σ) σ
      ((⟨sk,rs,wk,true⟩ : KRKState).map symX) :=
    ⟨⟨symX.ne_iff.2 hq.1.1,symX.ne_iff.2 hq.1.2.1,
      symX.ne_iff.2 hq.1.2.2.1,rfl⟩,rfl⟩
  apply krk_bound_transport symX hcanon rfl
  · simpa only [KRKState.map_map] using hq
  · apply pivot_right hcanon (by exact hsy) (by exact hwy)
    · change 7-sk.1.val=3 ∨ 7-sk.1.val=4; omega
    · change (7-sk.1.val)+2≤7-wk.1.val
      simp only [absDiff] at hx; omega

end EndgameChess.Rules.KRKCentral
