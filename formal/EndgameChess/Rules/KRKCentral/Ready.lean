import EndgameChess.Rules.KRKCentral.Full

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Ready central costs are11,29,47,59,71,83. The advance calls Full on
the next rank; it never silently carries a readiness premise through restoration. -/
theorem ready_bound {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val) (hwy : rs.2.val<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4) (hf : 2≤absDiff rs.1.val wk.1.val) :
    MateWithin σ (readyCost (7-rs.2.val)) q := by
  by_cases hsmall : 7-rs.2.val≤3
  · have hh := small_central_bound hq hsy rfl hwy hs
    simpa only [readyCost,ite_eq_left hsmall] using hh
  have child : CentralBound σ (rs.2.val+1) (fullCost (7-(rs.2.val+1))) := by
    intro p s r w hp hsp hrp hwp hsc
    exact full_bound hp hsp hrp hwp hsc
  have he : ExitBound σ rs.2.val (fullCost (7-(rs.2.val+1))+8) := by
    intro p hp
    have hh := exit_step_bound child p hp
    simpa only [ite_eq_right (show rs.2.val≠6 by omega)] using hh
  apply mateWithin_mono (ready_cut_bound he hq hsy rfl hwy hs hf)
  simp only [readyCost,fullCost]
  split <;> (try split) <;> omega

end EndgameChess.Rules.KRKCentral
