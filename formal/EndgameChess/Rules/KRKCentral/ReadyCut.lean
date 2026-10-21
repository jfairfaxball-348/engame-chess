import EndgameChess.Rules.KRKCentral.Pivot

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- A ready central wall exits or cuts after at most one pair. The exit
tail costs E and the complete protected-cut tail costs59. -/
theorem ready_cut_bound {σ : Colour} {y E : Nat}
    (hexit : ExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=y) (hry : rs.2.val=y) (hwy : y<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4) (hf : 2≤absDiff rs.1.val wk.1.val) :
    MateWithin σ (max (E+2) 61) q := by
  by_cases hup : y+2≤wk.2.val
  · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,by omega,by omega,hf,Or.inl hup⟩) (by omega)
  by_cases halign : sk.1.val=wk.1.val
  · exact mateWithin_mono (hexit q ⟨sk,rs,wk,hq,hsy,hry,hwy,by omega,by omega,hf,Or.inr halign⟩) (by omega)
  have hband : wk.2.val=rs.2.val+1 := by omega
  by_cases hwide : 2≤absDiff sk.1.val wk.1.val
  · exact mateWithin_mono (pivot_bound hq (by omega) hband hs hwide) (by omega)
  let nr : Square := (wallWaitFile rs.1 wk.1,rs.2)
  have hchoice := wall_wait_choice rs.1 wk.1
  have hdistinct : nr≠rs := by
    intro he; apply hchoice.1; exact congrArg Prod.fst he
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
    (nr := nr) rfl hdistinct hchoice.2
  apply mateWithin_mono (n := (max E 59)+2) ?_ (by omega)
  apply mateWithin_pair (σ := σ) hq.2 hl hm.2 hne
  intro v hv
  obtain ⟨t,hmt,hty,hft,hunit,hshape⟩ := hall v hv
  rcases hshape hband with hu | ⟨htband,hdx⟩
  · exact mateWithin_mono (hexit v ⟨sk,nr,t,hmt,hsy,hry,by omega,by omega,by omega,hft,Or.inl (by omega)⟩) (by omega)
  by_cases hal : sk.1.val=t.1.val
  · exact mateWithin_mono (hexit v ⟨sk,nr,t,hmt,hsy,hry,by omega,by omega,by omega,hft,Or.inr hal⟩) (by omega)
  have hwt : 2≤absDiff sk.1.val t.1.val := by simp only [absDiff] at *; omega
  exact mateWithin_mono (pivot_bound hmt (by change sk.2.val+1=rs.2.val; omega)
    (by exact htband) hs hwt) (by omega)

end EndgameChess.Rules.KRKCentral
