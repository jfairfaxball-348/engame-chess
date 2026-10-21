import EndgameChess.Rules.KRKCentral.Costs

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- The complete full-central wall induction: costs at heights1..6 are
11,29,47,63,75,87. Its restoration endpoint is FULL, not assumed ready. -/
theorem full_bound {σ : Colour} {y : Nat} : CentralBound σ y (fullCost (7-y)) := by
  suffices main : ∀ n y, 7-y=n → CentralBound σ y (fullCost n) by
    intro q sk rs wk hq hsy hry hwy hs
    exact main (7-y) y rfl hq hsy hry hwy hs
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro y hn q sk rs wk hq hsy hry hwy hs
    have hy : y≤6 := by omega
    have hn1 : 1≤n := by omega
    by_cases hsmall : n≤3
    · have hh := small_central_bound hq hsy hry hwy hs
      simpa only [fullCost,hn,ite_eq_left hsmall] using hh
    have child : CentralBound σ (y+1) (fullCost (n-1)) := by
      intro p s r w hp hsp hrp hwp hsc
      exact ih (n-1) (by omega) (y+1) (by omega) hp hsp hrp hwp hsc
    have he : ExitBound σ y (fullCost (n-1)+8) := by
      intro p hp
      have hh := exit_step_bound child p hp
      simpa only [ite_eq_right (show y≠6 by omega)] using hh
    apply mateWithin_mono (full_cut_bound he hq hsy hry hwy hs)
    simp only [fullCost]
    split <;> (try split) <;> omega

end EndgameChess.Rules.KRKCentral
