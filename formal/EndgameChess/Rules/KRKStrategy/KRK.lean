import EndgameChess.Rules.KRKStrategy.Line
import EndgameChess.Rules.KRKStrategy.Terminal
import EndgameChess.Rules.KRKBound.Arrival
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Every legal strong-turn KRK arrival admits the key-simple all-defence rank strategy. -/
theorem krk_key_simple_strategy {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (ha : ∃ p, Legal p q) :
    MateWithin σ 508 q ∧ strategyRank σ q ≤ 508 ∧
    (∀ {tail : List Position}, StrategyLine σ (q :: tail) →
      List.Pairwise (fun a b => RawRepetition.key a ≠ RawRepetition.key b) (q :: tail) ∧
      (q :: tail).length ≤ 509) := by
  have bound := krk_strong_arrival_bound hk ht ha
  have rank := (strategy_rank_spec ⟨508, bound⟩).2.1 508 bound
  refine ⟨bound, rank, ?_⟩
  intro tail line
  obtain ⟨_, _, distinct, length⟩ := strategy_line_certificate line
  exact ⟨distinct, by omega⟩
end EndgameChess.Rules
