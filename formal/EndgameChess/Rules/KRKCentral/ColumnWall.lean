import EndgameChess.Rules.KRKCentral.ExitStep

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- The interior close wall produced by guarded entry has the needed
18*n+1 cap. The next rank uses the uncut central bound, so this proof does
not depend on the guarded cut it will itself support. -/
theorem column_wall_bound {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val) (hwy : rs.2.val<wk.2.val)
    (hs1 : 1≤sk.1.val) (hs6 : sk.1.val≤6) :
    MateWithin σ (18*(7-rs.2.val)+1) q := by
  have hc : CentralBound σ (rs.2.val+1) (18*((7-(rs.2.val+1))-1)+11) := by
    intro p s r w hp hsp hrp hwp hsc
    exact small_central_bound hp hsp hrp hwp hsc
  apply mateWithin_mono (column_bound (exit_step_bound hc) hq hsy rfl hwy hs1 hs6)
  split <;> omega

end EndgameChess.Rules.KRKCentral
