import EndgameChess.Rules.KRKWinning.Safety
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding KRKTermination

/-- On concrete KRK Region the fuel bound upgrades safe F-choices to actual winning. -/
theorem actual_win_of_force {σ c : Colour} {s : State} (region : Region σ s)
    (win : F c s) : ActualWin c s := by
  obtain ⟨π,legal,safe⟩ := winning_safety win
  refine ⟨π,fuel s,legal,safe,?_⟩
  intro n t path
  have bound := (policy_path_bound region path).2.2
  omega
end EndgameChess.Rules.KRKWinning
