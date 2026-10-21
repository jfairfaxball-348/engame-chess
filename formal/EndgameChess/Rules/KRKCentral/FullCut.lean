import EndgameChess.Rules.KRKCentral.ReadyCut

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Repairing a threatened rook costs one pair before the ready-cut bound. -/
theorem full_cut_bound {σ : Colour} {y E : Nat}
    (hexit : ExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=y) (hry : rs.2.val=y) (hwy : y<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4) :
    MateWithin σ (max (E+4) 61) q := by
  by_cases hf : 2≤absDiff rs.1.val wk.1.val
  · exact mateWithin_mono (ready_cut_bound hexit hq hsy hry hwy hs hf) (by omega)
  let nr : Square := (wallFarFile wk.1,rs.2)
  have hfar : 4≤absDiff nr.1.val wk.1.val := wall_far_margin wk.1
  have hdistinct : nr≠rs := by
    intro he; rw [he] at hfar; omega
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
    (nr := nr) rfl hdistinct (by omega)
  apply mateWithin_mono (n := (max (E+2) 59)+2) ?_ (by omega)
  apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
  intro v hv
  obtain ⟨t,hmt,hty,hft,_,_⟩ := hall v hv
  exact ready_cut_bound hexit hmt hsy hry (by omega) hs hft

end EndgameChess.Rules.KRKCentral
