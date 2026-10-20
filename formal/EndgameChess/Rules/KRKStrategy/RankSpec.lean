import EndgameChess.Rules.KRKStrategy.RankDefinitions
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Specification, minimality and the zero-rank boundary all retain the win premise. -/
theorem strategy_rank_spec {σ : Colour} {q : Position} (h : ForceMate σ q) :
    MateWithin σ (strategyRank σ q) q ∧
    (∀ n, MateWithin σ n q → strategyRank σ q ≤ n) ∧
    (strategyRank σ q = 0 ↔ MateGoal σ q) := by
  classical
  have spec := Classical.choose_spec (strategy_least_budget h)
  have he : strategyRank σ q = Classical.choose (strategy_least_budget h) := by
    simp only [strategyRank, dite_eq_left h]
  refine ⟨he ▸ spec.1, ?_, ?_⟩
  · intro n hn
    rw [he]
    exact spec.2 n hn
  · constructor
    · intro hz
      have win := he ▸ spec.1
      rw [hz] at win
      exact win
    · intro goal
      have le := spec.2 0 goal
      omega
end EndgameChess.Rules
