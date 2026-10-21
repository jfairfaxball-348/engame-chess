import EndgameChess.Rules.KRKCentral.Positive

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- The single lower-band offset1 wait used after an aligned rook repair.
Its sharper even tail is necessary to keep central pursuit within five pairs. -/
theorem wait_even_bound (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : ExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=y) (hry : rs.2.val=y) (hwy : wk.2.val=y+1)
    (hs : 3≤pursuitFile d sk) (hs6 : pursuitFile d sk≤6)
    (hw : pursuitFile d wk=pursuitFile d sk+1) :
    MateWithin σ (E+2*((6-pursuitFile d sk)+1)) q := by
  have phys : 1≤sk.1.val ∧ sk.1.val≤6 := by
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
  let k : Fin 8 := if pursuitFile d rs=0 then 1 else 0
  let nr : Square := backRook d k rs
  have hnr : pursuitFile d nr=k.val := by
    cases d <;> simp [nr,backRook,backFile,pursuitFile] <;> omega
  have hk : k.val≤1 := by dsimp [k]; split <;> decide
  have hdistinct : nr≠rs := by
    intro he
    have hsame : pursuitFile d nr=pursuitFile d rs := congrArg (pursuitFile d) he
    dsimp [k] at hnr
    split at hnr <;> simp only [Fin.val_zero,Fin.val_one] at hnr <;> omega
  have hnry : nr.2=rs.2 := rfl
  have hf3 : 3≤absDiff nr.1.val wk.1.val := by
    rw [←pursuit_absDiff d nr wk]; simp only [absDiff]; omega
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega) hnry hdistinct hf3
  apply mateWithin_mono (n := (E+2*(6-pursuitFile d sk))+2) ?_ (by omega)
  apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
  intro v hv
  obtain ⟨t,hmt,hty,hft,hunit,hshape⟩ := hall v hv
  rcases hshape (by omega) with hu | ⟨htband,hdx⟩
  · exact mateWithin_mono (hexit v ⟨sk,nr,t,hmt,hsy,by exact hry,by omega,
      phys.1,phys.2,hft,Or.inl (by omega)⟩) (by omega)
  · have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)=1 := by
      rw [pursuit_absDiff]; exact hdx
    have hev : ∃ j, pursuitFile d t=pursuitFile d sk+2*j := by
      by_cases hright : pursuitFile d wk<pursuitFile d t
      · exact ⟨1,by simp only [absDiff] at hdx'; omega⟩
      · exact ⟨0,by simp only [absDiff] at hdx'; omega⟩
    exact back_even_bound d hexit hmt hsy (by exact hry) (by omega) hs hs6 (by omega) hev

end EndgameChess.Rules.KRKCentral
