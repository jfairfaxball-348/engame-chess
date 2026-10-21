import EndgameChess.Rules.KRKCentral.PrepPair

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Centralise an arbitrary wall and end READY, including a possible final
rescue. Every rescue gives margin3 after the weak reply, paying for two king
pairs before the next possible repair. -/
theorem prep_bound {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val<rs.2.val) (hw : rs.2.val<wk.2.val) :
    MateWithin σ (readyCost (7-rs.2.val)+prepCost (prepDistance rs.2.val sk)) q := by
  suffices main : ∀ n y, ∀ {q : Position} {sk rs wk : Square},
      Matches q σ ⟨sk,rs,wk,true⟩ → sk.2.val<rs.2.val → rs.2.val<wk.2.val →
      rs.2.val=y → prepDistance y sk=n →
      MateWithin σ (readyCost (7-y)+prepCost n) q by
    exact main _ _ hq hb hw rfl rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro y q sk rs wk hq hb hw hry hn
    have finish {p : Position} {s r w : Square}
        (hm : Matches p σ ⟨s,r,w,true⟩) (hby : s.2.val<r.2.val)
        (hwy : r.2.val<w.2.val) (hry' : r.2.val=y)
        (hz : prepDistance y s=0) (hf : 2≤absDiff r.1.val w.1.val) :
        MateWithin σ (readyCost (7-y)) p := by
      have hs : s.1.val=3 ∨ s.1.val=4 := by
        simp only [prepDistance,centreDistance] at hz
        split at hz <;> (try split at hz) <;> omega
      have hsy : s.2.val+1=r.2.val := by simp only [prepDistance] at hz; omega
      simpa only [hry'] using ready_bound hm hsy hwy hs hf
    by_cases hz : n=0
    · by_cases hf : 2≤absDiff rs.1.val wk.1.val
      · exact mateWithin_mono (finish hq hb hw hry (by omega) hf) (by simp only [prepCost]; omega)
      let nr : Square := (wallFarFile wk.1,rs.2)
      have hfar : 4≤absDiff nr.1.val wk.1.val := wall_far_margin wk.1
      have hdistinct : nr≠rs := by intro he; rw [he] at hfar; omega
      obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq hb hw (nr := nr) rfl hdistinct (by omega)
      apply mateWithin_mono (n := readyCost (7-y)+2) ?_ (by simp only [prepCost]; omega)
      apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
      intro v hv
      obtain ⟨t,hmt,hty,hft,_,_⟩ := hall v hv
      exact finish hmt (by exact hb) (by exact hty) hry (by omega) hft
    have good : ∀ {v : Position} {rr ww : Square},
        Matches v σ ⟨sk,rr,ww,true⟩ → rr.2.val=y → y<ww.2.val →
        3≤absDiff rr.1.val ww.1.val →
        MateWithin σ (readyCost (7-y)+2*(n+n/2)) v := by
      intro v rr ww hv hrr hww hmargin
      obtain ⟨su,c,hsu,hdist,hl,hm,hne,hall⟩ := prep_pair hv (by omega) (by omega)
        (by simpa only [hrr,hn] using (show 0<n by omega)) (by omega)
      by_cases hone : n=1
      · apply mateWithin_mono (n := readyCost (7-y)+2) ?_ (by omega)
        apply mateWithin_pair (σ := σ) hv.2 hl hm.2 hne
        intro z hzz
        obtain ⟨t,hmt,hty,hunit⟩ := hall z hzz
        have hft : 2≤absDiff rr.1.val t.1.val := by simp only [absDiff] at *; omega
        exact finish hmt hsu hty hrr (by rw [hrr] at hdist; omega) hft
      apply mateWithin_mono (n := (readyCost (7-y)+prepCost (n-2))+4) ?_
        (by simp only [prepCost]; omega)
      apply mateWithin_pair (σ := σ) hv.2 hl hm.2 hne
      intro z hzz
      obtain ⟨t,hmt,hty,hunit⟩ := hall z hzz
      have hft : 2≤absDiff rr.1.val t.1.val := by simp only [absDiff] at *; omega
      obtain ⟨ss,cc,hss,hdd,hll,hmm,hnee,halls⟩ := prep_pair hmt hsu hty
        (by rw [hrr] at hdist ⊢; omega) hft
      apply mateWithin_pair (σ := σ) hmt.2 hll hmm.2 hnee
      intro zz hzzz
      obtain ⟨tt,hmtt,htty,_⟩ := halls zz hzzz
      exact ih (n-2) (by omega) y hmtt hss htty hrr (by rw [hrr] at hdist hdd; omega)
    by_cases hf : 3≤absDiff rs.1.val wk.1.val
    · exact mateWithin_mono (good hq hry (by omega) hf) (by simp only [prepCost]; omega)
    let nr : Square := (wallFarFile wk.1,rs.2)
    have hfar : 4≤absDiff nr.1.val wk.1.val := wall_far_margin wk.1
    have hdistinct : nr≠rs := by intro he; rw [he] at hfar; omega
    obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq hb hw (nr := nr) rfl hdistinct (by omega)
    apply mateWithin_mono (n := (readyCost (7-y)+2*(n+n/2))+2) ?_ (by simp only [prepCost]; omega)
    apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
    intro v hv
    obtain ⟨t,hmt,hty,hft,hunit,_⟩ := hall v hv
    have hf3 : 3≤absDiff nr.1.val t.1.val := by simp only [absDiff] at *; omega
    exact good hmt hry (by omega) hf3

end EndgameChess.Rules.KRKCentral
