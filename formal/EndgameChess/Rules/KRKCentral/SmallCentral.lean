import EndgameChess.Rules.KRKCentral.Restoration

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- The uncut central induction. Its first three heights give 11,29,47 plies
and are the noncircular inputs to the protected perpendicular cut. -/
theorem small_central_bound {σ : Colour} {y : Nat} :
    CentralBound σ y (18*((7-y)-1)+11) := by
  suffices main : ∀ n y, 7-y=n → CentralBound σ y (18*(n-1)+11) by
    intro q sk rs wk hq hsy hry hwy hs
    exact main (7-y) y rfl hq hsy hry hwy hs
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro y hn q sk rs wk hq hsy hry hwy hs
    have hy : y≤6 := by omega
    have hn1 : 1≤n := by omega
    have child (hn2 : 2≤n) : CentralBound σ (y+1) (18*(n-2)+11) := by
      have he : n-1-1=n-2 := by omega
      intro p s r w hp hsp hrp hwp hsc
      simpa only [he] using ih (n-1) (by omega) (y+1) (by omega) hp hsp hrp hwp hsc
    have hexit : ExitBound σ y (18*(n-1)+1) := by
      intro p hp
      obtain ⟨s,r,w,hm,hsy',hry',hwy',hs1,hs6,hf,hupper | halign⟩ := hp
      · have hn2 : 2≤n := by omega
        obtain ⟨nr,c,hnrx,hnry,hl,hmc,hne,hall⟩ := rank_two_pair hm (by omega) (by omega) hf
        apply mateWithin_mono (n := (18*(n-2)+11+6)+2) ?_ (by omega)
        apply mateWithin_pair (σ := σ) hm.2 hl hmc.2 hne
        intro v hv
        obtain ⟨t,hmt,hty,_⟩ := hall v hv
        exact restoration_bound (child hn2) hmt (by omega) (by omega) (by omega) hs1 hs6
      · by_cases hup : y+2≤w.2.val
        · have hn2 : 2≤n := by omega
          obtain ⟨nr,c,hnrx,hnry,hl,hmc,hne,hall⟩ := rank_two_pair hm (by omega) (by omega) hf
          apply mateWithin_mono (n := (18*(n-2)+11+6)+2) ?_ (by omega)
          apply mateWithin_pair (σ := σ) hm.2 hl hmc.2 hne
          intro v hv
          obtain ⟨t,hmt,hty,_⟩ := hall v hv
          exact restoration_bound (child hn2) hmt (by omega) (by omega) (by omega) hs1 hs6
        have ho : Opposed s w := ⟨halign,by omega⟩
        obtain ⟨c,hl,hmc,hgoal | ⟨hne,hall⟩⟩ := krk_opposition_check_two hm ho hf (by omega)
        · exact mateWithin_mono (mateWithin_choose (σ := σ) (n := 0) hm.2 hl hgoal) (by omega)
        · have hn2 : 2≤n := by
            obtain ⟨v,hv⟩ := hne
            obtain ⟨t,hmt,hty,_⟩ := hall v hv
            change t.2.val=w.2.val+1 at hty
            omega
          apply mateWithin_mono (n := (18*(n-2)+11+6)+2) ?_ (by omega)
          apply mateWithin_pair (σ := σ) hm.2 hl hmc.2 hne
          intro v hv
          obtain ⟨t,hmt,hty,_⟩ := hall v hv
          change t.2.val=w.2.val+1 at hty
          apply restoration_bound (child hn2) hmt (by omega) ?_ ?_ hs1 hs6
          · change w.2.val=y+1; omega
          · change y+1<t.2.val; omega
    exact mateWithin_mono (central_bound hexit hq hsy hry hwy hs) (by omega)

end EndgameChess.Rules.KRKCentral
