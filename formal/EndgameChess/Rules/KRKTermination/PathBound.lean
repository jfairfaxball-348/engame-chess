import EndgameChess.Rules.KRKTermination.Step
namespace EndgameChess.Rules.KRKTermination
open EndgameChess.KK
open RawHistoryLayer

/-- Every finite admitted path, including unchosen legal moves, spends its length in fuel. -/
theorem path_bound {σ : Colour} {s t : State} {n : Nat} (region : Region σ s)
    (path : Path n s t) : Region σ t ∧ fuel t + n ≤ fuel s := by
  induction path with
  | refl => exact ⟨region, by omega⟩
  | cons step tail ih =>
    obtain ⟨nextRegion, decrease⟩ := step_decreases region step
    obtain ⟨endRegion, bound⟩ := ih nextRegion
    exact ⟨endRegion, by omega⟩
end EndgameChess.Rules.KRKTermination
