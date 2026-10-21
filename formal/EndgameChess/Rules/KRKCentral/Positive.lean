import EndgameChess.Rules.KRKCentral.Back

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Positive-oriented central pursuit, with arbitrary incoming rook file.
A single relocation enters Back; otherwise each king pair decreases the
remaining file distance. Only the endpoint bound is assumed. -/
theorem positive_bound (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : ExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=y) (hry : rs.2.val=y) (hwy : y<wk.2.val)
    (hs : 3≤pursuitFile d sk) (hw : pursuitFile d sk<pursuitFile d wk) :
    MateWithin σ (E+2*(8-pursuitFile d sk)) q := by
  suffices main : ∀ n, ∀ {q : Position} {sk rs wk : Square},
      Matches q σ ⟨sk,rs,wk,true⟩ → sk.2.val+1=y → rs.2.val=y → y<wk.2.val →
      3≤pursuitFile d sk → pursuitFile d sk<pursuitFile d wk →
      8-pursuitFile d sk=n → MateWithin σ (E+2*n) q by
    exact main _ hq hsy hry hwy hs hw rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q sk rs wk hq hsy hry hwy hs hw hn
    have hs6 : pursuitFile d sk≤6 := by have := pursuitFile_bound d wk; omega
    have phys : 1≤sk.1.val ∧ sk.1.val≤6 := by
      cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
    by_cases hex : y+2≤wk.2.val ∧ 2≤absDiff rs.1.val wk.1.val
    · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,phys.1,phys.2,hex.2,Or.inl hex.1⟩) (by omega)
    by_cases hchase : pursuitFile d sk+2≤pursuitFile d wk ∧ 3≤absDiff rs.1.val wk.1.val
    · have hband : wk.2.val=rs.2.val+1 := by omega
      obtain ⟨su,c,hsuy,hsux,hl,hm,hne,hall⟩ := krk_pursuit_king_move d hq
        (by omega) hband hchase.1 hchase.2
      have hsu : 3≤pursuitFile d su := by omega
      have hsu6 : pursuitFile d su≤6 := by have := pursuitFile_bound d wk; omega
      have suphys : 1≤su.1.val ∧ su.1.val≤6 := by
        cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
      apply mateWithin_mono (n := (E+2*(8-pursuitFile d su))+2) ?_ (by omega)
      apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
      intro v hv
      obtain ⟨t,hmt,hft,hunit,hshape⟩ := hall v hv
      by_cases hal : pursuitFile d t=pursuitFile d su
      · have hp : su.1.val=t.1.val := by
          cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at hal <;> omega
        exact mateWithin_mono (hexit v ⟨su,rs,t,hmt,by omega,hry,by
          rcases hshape with hu | ⟨hty,_⟩ <;> omega,
          suphys.1,suphys.2,hft,Or.inr hp⟩) (by omega)
      rcases hshape with hu | ⟨hty,hdx⟩
      · exact mateWithin_mono (hexit v ⟨su,rs,t,hmt,by omega,hry,by omega,
          suphys.1,suphys.2,hft,Or.inl (by omega)⟩) (by omega)
      · have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)=1 := by
          rw [pursuit_absDiff]; exact hdx
        have hwt : pursuitFile d su<pursuitFile d t := by
          simp only [absDiff] at hdx'; omega
        exact ih _ (by omega) hmt (by omega) hry (by omega) hsu hwt rfl
    · let k : Fin 8 := if pursuitFile d rs=0 then 1 else 0
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
      apply mateWithin_mono (n := (E+2*((6-pursuitFile d sk)+1))+2) ?_ (by omega)
      apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
      intro v hv
      obtain ⟨t,hmt,hty,hft,hunit,hshape⟩ := hall v hv
      have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)≤1 := by
        rw [pursuit_absDiff]; exact hunit
      have hwt : pursuitFile d sk≤pursuitFile d t := by
        simp only [absDiff] at hdx'; omega
      exact back_bound d hexit hmt hsy (by exact hry) (by omega) hs hs6 (by omega) hwt

end EndgameChess.Rules.KRKCentral
