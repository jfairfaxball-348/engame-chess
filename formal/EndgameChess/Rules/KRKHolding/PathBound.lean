import EndgameChess.Rules.KRKHolding.Definitions
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Every policy path is an actual admitted path and obeys the universal fuel bound. -/
theorem policy_path_bound {σ c : Colour} {π : Policy} {s t : State} {n : Nat}
    (region : Region σ s) (path : PolicyPath c π n s t) :
    Path n s t ∧ Region σ t ∧ fuel t + n ≤ fuel s := by
  have actual : Path n s t := by
    induction path with
    | refl => exact .refl _
    | cons edge _ _ ih => exact .cons edge (ih (step_decreases region edge).1)
  exact ⟨actual,path_bound region actual⟩
end EndgameChess.Rules.KRKHolding
