import EndgameChess.Rules.KRKStrategy.RankSpec
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Equal normalized keys have equal least budgets, including the total-default case. -/
theorem strategy_rank_key {q r : Position} {σ : Colour}
    (hk : RawRepetition.key q = RawRepetition.key r) : strategyRank σ q = strategyRank σ r := by
  classical
  have wins : ForceMate σ q ↔ ForceMate σ r := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (strategy_key_budget hk σ n).mp hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, (strategy_key_budget hk σ n).mpr hn⟩
  by_cases hq : ForceMate σ q
  · have hr := wins.mp hq
    obtain ⟨qs, qm, _⟩ := strategy_rank_spec hq
    obtain ⟨rs, rm, _⟩ := strategy_rank_spec hr
    exact Nat.le_antisymm (qm _ ((strategy_key_budget hk σ _).mpr rs))
      (rm _ ((strategy_key_budget hk σ _).mp qs))
  · have hr : ¬ForceMate σ r := fun h => hq (wins.mpr h)
    simp only [strategyRank, dite_eq_right hq, dite_eq_right hr]
end EndgameChess.Rules
