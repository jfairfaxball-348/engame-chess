import EndgameChess.Rules.KRKCentral.BackEven

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Back-rook pursuit costs at most one waiting pair beyond king progress.
The wait makes the lower-band offset even, so BackEven supplies its tail. -/
theorem back_bound (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : ExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=y) (hry : rs.2.val=y) (hwy : y<wk.2.val)
    (hs : 3≤pursuitFile d sk) (hs6 : pursuitFile d sk≤6)
    (hr : pursuitFile d rs≤1) (hw : pursuitFile d sk≤pursuitFile d wk) :
    MateWithin σ (E+2*((6-pursuitFile d sk)+1)) q := by
  suffices main : ∀ n, ∀ {q : Position} {sk rs wk : Square},
      Matches q σ ⟨sk,rs,wk,true⟩ → sk.2.val+1=y → rs.2.val=y → y<wk.2.val →
      3≤pursuitFile d sk → pursuitFile d sk≤6 → pursuitFile d rs≤1 →
      pursuitFile d sk≤pursuitFile d wk →
      6-pursuitFile d sk=n → MateWithin σ (E+2*(n+1)) q by
    exact main _ hq hsy hry hwy hs hs6 hr hw rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q sk rs wk hq hsy hry hwy hs hs6 hr hw hn
    have phys : 1≤sk.1.val ∧ sk.1.val≤6 := by
      cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
    have hf : 2≤absDiff rs.1.val wk.1.val := by
      rw [←pursuit_absDiff d rs wk]; simp only [absDiff]; omega
    by_cases hup : y+2≤wk.2.val
    · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,phys.1,phys.2,hf,Or.inl hup⟩) (by omega)
    by_cases halign : sk.1.val=wk.1.val
    · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,phys.1,phys.2,hf,Or.inr halign⟩) (by omega)
    have hnot : pursuitFile d sk ≠ pursuitFile d wk := by
      intro he; apply halign
      cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at he <;> omega
    by_cases hone : pursuitFile d wk=pursuitFile d sk+1
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
      apply mateWithin_mono (n := (E+2*n)+2) ?_ (by omega)
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
        simpa only [←hn] using back_even_bound d hexit hmt hsy
          (by exact hry) (by omega) hs hs6 (by omega) hev
    · have hwide : pursuitFile d sk+2≤pursuitFile d wk := by omega
      have hf3 : 3≤absDiff rs.1.val wk.1.val := by
        rw [←pursuit_absDiff d rs wk]; simp only [absDiff]; omega
      obtain ⟨su,c,hsuy,hsux,hl,hm,hne,hall⟩ :=
        krk_pursuit_king_move d hq (by omega) (by omega) hwide hf3
      have hsu : 3≤pursuitFile d su := by omega
      have hsu6 : pursuitFile d su≤6 := by have := pursuitFile_bound d wk; omega
      have suphys : 1≤su.1.val ∧ su.1.val≤6 := by
        cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
      apply mateWithin_mono (n := (E+2*((6-pursuitFile d su)+1))+2) ?_ (by omega)
      apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
      intro v hv
      obtain ⟨t,hmt,hft,hunit,hshape⟩ := hall v hv
      rcases hshape with hu | ⟨hty,hdx⟩
      · exact mateWithin_mono (hexit v ⟨su,rs,t,hmt,by omega,hry,by omega,
          suphys.1,suphys.2,hft,Or.inl (by omega)⟩) (by omega)
      · have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)=1 := by
          rw [pursuit_absDiff]; exact hdx
        have hwt : pursuitFile d su≤pursuitFile d t := by
          simp only [absDiff] at hdx'; omega
        exact ih _ (by omega) hmt (by omega) hry (by omega) hsu hsu6 hr hwt rfl

end EndgameChess.Rules.KRKCentral
