import EndgameChess.Rules.KRKCentral.Central

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Restore the full central close wall after one rook-rank advance.
One rescue and at most two king pairs cost six plies. No ready margin is
asserted at the output of the final king pair. -/
theorem restoration_bound {σ : Colour} {y E : Nat}
    (hcentral : CentralBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+2=y) (hry : rs.2.val=y) (hwy : y<wk.2.val)
    (hs1 : 1≤sk.1.val) (hs6 : sk.1.val≤6) : MateWithin σ (E+6) q := by
  have catch_up : ∀ {v : Position} {rr ww : Square},
      Matches v σ ⟨sk,rr,ww,true⟩ → rr.2.val=y → y<ww.2.val →
      3≤absDiff rr.1.val ww.1.val → MateWithin σ (E+4) v := by
    intro v rr ww hv hrr hww hmargin
    let x : Fin 8 := if h : sk.1.val<3 then ⟨sk.1.val+1,by omega⟩
      else if h : 4<sk.1.val then ⟨sk.1.val-1,by omega⟩ else sk.1
    let su : Square := (x,⟨sk.2.val+1,by omega⟩)
    have hx : 2≤x.val ∧ x.val≤5 ∧ absDiff sk.1.val x.val≤1 := by
      dsimp [x]; split <;> (try split) <;> simp only [absDiff] <;> omega
    have hsuy : su.2.val=sk.2.val+1 := rfl
    have hstep : dInf sk su=1 := by
      change max (absDiff sk.1.val x.val) (absDiff sk.2.val (sk.2.val+1))=1
      simp only [absDiff] at *; omega
    obtain ⟨c,hl,hm,hne,hall⟩ := king_below_pair hv hstep (by omega) (by omega) (by omega)
    apply mateWithin_mono (n := (E+2)+2) ?_ (by omega)
    apply mateWithin_pair (σ := σ) hv.2 hl hm.2 hne
    intro z hz
    obtain ⟨t,hmt,hty,hunit⟩ := hall z hz
    have hft : 2≤absDiff rr.1.val t.1.val := by simp only [absDiff] at *; omega
    by_cases hcx : x.val=3 ∨ x.val=4
    · exact mateWithin_mono (hcentral hmt (by omega) hrr (by omega) hcx) (by omega)
    let tx : Fin 8 := if x.val<3 then 3 else 4
    let tu : Square := (tx,su.2)
    have htx : tx.val=3 ∨ tx.val=4 := by dsimp [tx]; split <;> omega
    have htstep : dInf su tu=1 := by
      change max (absDiff x.val tx.val) (absDiff su.2.val su.2.val)=1
      dsimp [tx]; split <;> simp only [absDiff] <;> omega
    obtain ⟨cc,hll,hmm,hnee,halls⟩ := king_below_pair hmt htstep (by
      change su.2.val<rr.2.val; omega) hty hft
    apply mateWithin_pair (σ := σ) hmt.2 hll hmm.2 hnee
    intro zz hzz
    obtain ⟨tt,hmtt,htty,_⟩ := halls zz hzz
    exact hcentral hmtt (by change su.2.val+1=y; omega) hrr (by omega) htx
  by_cases hf : 3≤absDiff rs.1.val wk.1.val
  · exact mateWithin_mono (catch_up hq hry hwy hf) (by omega)
  let nr : Square := (wallFarFile wk.1,rs.2)
  have hfar : 4≤absDiff nr.1.val wk.1.val := wall_far_margin wk.1
  have hdistinct : nr≠rs := by
    intro he
    have hsame : nr.1.val=rs.1.val := congrArg (fun s : Square => s.1.val) he
    rw [hsame] at hfar; omega
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
    (nr := nr) rfl hdistinct (by omega)
  apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
  intro v hv
  obtain ⟨t,hmt,hty,hft,hunit,_⟩ := hall v hv
  have hf3 : 3≤absDiff nr.1.val t.1.val := by simp only [absDiff] at *; omega
  exact catch_up hmt hry (by omega) hf3

end EndgameChess.Rules.KRKCentral
