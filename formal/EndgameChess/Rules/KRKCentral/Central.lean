import EndgameChess.Rules.KRKCentral.WaitEven

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Any full central close wall reaches the ready upper/aligned exit within
ten plies, including initially aligned positions needing a rook repair. -/
theorem central_bound {σ : Colour} {y E : Nat}
    (hexit : ExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=y) (hry : rs.2.val=y) (hwy : y<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4) : MateWithin σ (E+10) q := by
  by_cases hright : sk.1.val<wk.1.val
  · exact mateWithin_mono (positive_bound true hexit hq hsy hry hwy
      (by simp only [pursuitFile,↓reduceIte]; omega)
      (by simpa only [pursuitFile,↓reduceIte] using hright))
      (by simp only [pursuitFile,↓reduceIte]; omega)
  by_cases hleft : wk.1.val<sk.1.val
  · exact mateWithin_mono (positive_bound false hexit hq hsy hry hwy
      (by simp only [pursuitFile,Bool.false_eq_true,↓reduceIte]; omega)
      (by simp only [pursuitFile,Bool.false_eq_true,↓reduceIte]; omega))
      (by simp only [pursuitFile,Bool.false_eq_true,↓reduceIte]; omega)
  have halign : sk.1.val=wk.1.val := by omega
  by_cases hf : 2≤absDiff rs.1.val wk.1.val
  · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,by omega,by omega,hf,Or.inr halign⟩) (by omega)
  let nr : Square := (wallFarFile wk.1,rs.2)
  have hfar : 4≤absDiff nr.1.val wk.1.val := wall_far_margin wk.1
  have hdistinct : nr≠rs := by
    intro he
    have hsame : nr.1.val=rs.1.val := congrArg (fun s : Square => s.1.val) he
    rw [hsame] at hfar
    omega
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
    (nr := nr) rfl hdistinct (by omega)
  apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
  intro v hv
  obtain ⟨t,hmt,hty,hft,hunit,hshape⟩ := hall v hv
  by_cases hup : y+2≤t.2.val
  · exact mateWithin_mono (hexit v ⟨sk,nr,t,hmt,hsy,hry,by omega,by omega,by omega,hft,Or.inl hup⟩) (by omega)
  by_cases hal : sk.1.val=t.1.val
  · exact mateWithin_mono (hexit v ⟨sk,nr,t,hmt,hsy,hry,by omega,by omega,by omega,hft,Or.inr hal⟩) (by omega)
  have hband : t.2.val=y+1 := by omega
  by_cases ht : sk.1.val<t.1.val
  · exact mateWithin_mono (wait_even_bound true hexit hmt hsy hry hband
      (by simp only [pursuitFile,↓reduceIte]; omega)
      (by simp only [pursuitFile,↓reduceIte]; omega)
      (by simp only [pursuitFile,↓reduceIte,absDiff] at *; omega))
      (by simp only [pursuitFile,↓reduceIte]; omega)
  · exact mateWithin_mono (wait_even_bound false hexit hmt hsy hry hband
      (by simp only [pursuitFile,Bool.false_eq_true,↓reduceIte]; omega)
      (by simp only [pursuitFile,Bool.false_eq_true,↓reduceIte]; omega)
      (by simp only [pursuitFile,Bool.false_eq_true,↓reduceIte,absDiff] at *; omega))
      (by simp only [pursuitFile,Bool.false_eq_true,↓reduceIte]; omega)

end EndgameChess.Rules.KRKCentral
