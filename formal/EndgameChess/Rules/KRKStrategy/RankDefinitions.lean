import EndgameChess.Rules.KRKStrategy.LeastBudget
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Least clock-free mate budget; zero on nonwinning inputs is only a total default. -/
noncomputable def strategyRank (σ : Colour) (q : Position) : Nat := by
  classical
  exact if h : ForceMate σ q then Classical.choose (strategy_least_budget h) else 0
end EndgameChess.Rules
