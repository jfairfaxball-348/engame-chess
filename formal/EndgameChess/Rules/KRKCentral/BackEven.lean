import EndgameChess.Rules.KRKCentral.RankTwo

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Even-offset pursuit behind an oriented0/1 rook needs no further rook
tempo. This is C052's needed fast branch after its SINGLE waiting pair. -/
theorem back_even_bound (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : ExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=y) (hry : rs.2.val=y) (hwy : y<wk.2.val)
    (hs : 3≤pursuitFile d sk) (hs6 : pursuitFile d sk≤6)
    (hr : pursuitFile d rs≤1)
    (heven : ∃ k, pursuitFile d wk=pursuitFile d sk+2*k) :
    MateWithin σ (E+2*(6-pursuitFile d sk)) q := by
  suffices main : ∀ n, ∀ {q : Position} {sk rs wk : Square},
      Matches q σ ⟨sk,rs,wk,true⟩ → sk.2.val+1=y → rs.2.val=y → y<wk.2.val →
      3≤pursuitFile d sk → pursuitFile d sk≤6 → pursuitFile d rs≤1 →
      (∃ k, pursuitFile d wk=pursuitFile d sk+2*k) →
      6-pursuitFile d sk=n → MateWithin σ (E+2*n) q by
    exact main _ hq hsy hry hwy hs hs6 hr heven rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q sk rs wk hq hsy hry hwy hs hs6 hr heven hn
    obtain ⟨k,hk⟩ := heven
    have phys : 1≤sk.1.val ∧ sk.1.val≤6 := by
      cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
    have hf : 2≤absDiff rs.1.val wk.1.val := by
      rw [←pursuit_absDiff d rs wk]
      simp only [absDiff]; omega
    by_cases hup : y+2≤wk.2.val
    · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,phys.1,phys.2,hf,Or.inl hup⟩) (by omega)
    by_cases halign : sk.1.val=wk.1.val
    · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,phys.1,phys.2,hf,Or.inr halign⟩) (by omega)
    have hnot : pursuitFile d sk ≠ pursuitFile d wk := by
      intro he
      apply halign
      cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at he <;> omega
    have hwide : pursuitFile d sk+2≤pursuitFile d wk := by omega
    have hf3 : 3≤absDiff rs.1.val wk.1.val := by
      rw [←pursuit_absDiff d rs wk]
      simp only [absDiff]; omega
    obtain ⟨su,c,hsuy,hsux,hl,hm,hne,hall⟩ :=
      krk_pursuit_king_move d hq (by omega) (by omega) hwide hf3
    have hsu : 3≤pursuitFile d su := by omega
    have hsu6 : pursuitFile d su≤6 := by
      have := pursuitFile_bound d wk
      omega
    have suphys : 1≤su.1.val ∧ su.1.val≤6 := by
      cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
    apply mateWithin_mono (n := (E+2*(6-pursuitFile d su))+2) ?_ (by omega)
    apply mateWithin_pair hq.2 hl hm.2 hne
    intro v hv
    obtain ⟨t,hmt,hft,hunit,hshape⟩ := hall v hv
    have hsuy' : su.2.val+1=y := by omega
    rcases hshape with hu | ⟨hty,hdx⟩
    · exact mateWithin_mono (hexit v ⟨su,rs,t,hmt,hsuy',hry,by omega,
        suphys.1,suphys.2,hft,Or.inl (by omega)⟩) (by omega)
    · have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)=1 := by
        rw [pursuit_absDiff]; exact hdx
      have he : ∃ j, pursuitFile d t=pursuitFile d su+2*j := by
        by_cases hright : pursuitFile d wk<pursuitFile d t
        · exact ⟨k,by simp only [absDiff] at hdx'; omega⟩
        · exact ⟨k-1,by simp only [absDiff] at hdx'; omega⟩
      exact ih _ (by omega) hmt hsuy' hry (by omega) hsu hsu6 hr he rfl

end EndgameChess.Rules.KRKCentral
