import EndgameChess.Rules.KRKStrategy.RankKey
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Strong choices are restricted to strict rank descent; no weak reply is filtered. -/
def StrategyStep (σ : Colour) (q r : Position) : Prop :=
  Legal q r ∧ ForceMate σ q ∧ ForceMate σ r ∧ strategyRank σ r < strategyRank σ q

/-- A finite nonempty play line under this policy, with actual legal edges. -/
inductive StrategyLine (σ : Colour) : List Position → Prop
  | single (q : Position) : ForceMate σ q → StrategyLine σ [q]
  | cons {q r : Position} {tail : List Position} :
      StrategyStep σ q r → StrategyLine σ (r :: tail) → StrategyLine σ (q :: r :: tail)
end EndgameChess.Rules
