import EndgameChess.Rules.KRKStrategy.Progress
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Only actual named mate can stop the policy at a winning node. -/
theorem strategy_terminal {σ : Colour} {q : Position} (win : ForceMate σ q) :
    (¬∃ r, StrategyStep σ q r) ↔ MateGoal σ q := by
  constructor
  · intro none
    apply Classical.byContradiction
    intro ongoing
    obtain ⟨strong, weak⟩ := strategy_progress win ongoing
    by_cases turn : q.turn = σ
    · exact none (strong turn)
    · have other : q.turn = σ.opp := by cases σ <;> cases h : q.turn <;> simp_all [Colour.opp]
      obtain ⟨⟨r, legal⟩, all⟩ := weak other
      exact none ⟨r, all r legal⟩
  · intro goal
    have zero := (strategy_rank_spec win).2.2.mpr goal
    rintro ⟨r, step⟩
    have lt := step.2.2.2
    omega
end EndgameChess.Rules
