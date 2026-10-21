import EndgameChess.Rules.KRKCentral.Column

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- The ready exit either mates at rank6 or advances the wall and restores a
FULL central wall, costing at most eight plies before the supplied next bound. -/
theorem exit_step_bound {σ : Colour} {y C : Nat}
    (hnext : CentralBound σ (y+1) C) :
    ExitBound σ y (if y=6 then 1 else C+8) := by
  intro p hp
  obtain ⟨s,r,w,hm,hsy,hry,hwy,hs1,hs6,hf,hshape⟩ := hp
  have upper (hup : y+2≤w.2.val) : MateWithin σ (if y=6 then 1 else C+8) p := by
    have hy : y≠6 := by omega
    rw [ite_eq_right hy]
    obtain ⟨nr,c,hnrx,hnry,hl,hmc,hne,hall⟩ := rank_two_pair hm (by omega) (by omega) hf
    apply mateWithin_mono (n := (C+6)+2) ?_ (by omega)
    apply mateWithin_pair (σ := σ) hm.2 hl hmc.2 hne
    intro v hv
    obtain ⟨t,hmt,hty,_⟩ := hall v hv
    exact restoration_bound hnext hmt (by omega) (by omega) (by omega) hs1 hs6
  rcases hshape with hup | halign
  · exact upper hup
  by_cases hup : y+2≤w.2.val
  · exact upper hup
  have ho : Opposed s w := ⟨halign,by omega⟩
  obtain ⟨c,hl,hmc,hgoal | ⟨hne,hall⟩⟩ := krk_opposition_check_two hm ho hf (by omega)
  · exact mateWithin_mono (mateWithin_choose (σ := σ) (n := 0) hm.2 hl hgoal) (by split <;> omega)
  · have hy : y≠6 := by
      obtain ⟨v,hv⟩ := hne
      obtain ⟨t,hmt,hty,_⟩ := hall v hv
      change t.2.val=w.2.val+1 at hty
      omega
    rw [ite_eq_right hy]
    apply mateWithin_mono (n := (C+6)+2) ?_ (by omega)
    apply mateWithin_pair (σ := σ) hm.2 hl hmc.2 hne
    intro v hv
    obtain ⟨t,hmt,hty,_⟩ := hall v hv
    change t.2.val=w.2.val+1 at hty
    apply restoration_bound hnext hmt (by omega) ?_ ?_ hs1 hs6
    · change w.2.val=y+1; omega
    · change y+1<t.2.val; omega

end EndgameChess.Rules.KRKCentral
