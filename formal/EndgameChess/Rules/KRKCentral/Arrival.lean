import EndgameChess.Rules.KRKCentral.Wall
import EndgameChess.Rules.KRKSetup.Arrival

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK

/-- Every exact strong-turn KRK legal arrival has a97-ply clock-free cap. -/
theorem arrival97 {σ : Colour} {q : Position} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn=σ) (ha : ∃ p, Legal p q) :
    MateWithin σ 97 q := by
  have hwall : KRKWallBudget σ 93 := fun hm hb hw => wall93 hm hb hw
  exact setup_arrival_budget hwall hk ht ha

end EndgameChess.Rules.KRKCentral
