import EndgameChess.Rules.KRKCentral.Wall
import EndgameChess.Rules.KRKSetup.Arrival

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK

/-- Every exact strong-turn KRK legal arrival has a99-ply clock-free cap. -/
theorem arrival99 {σ : Colour} {q : Position} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn=σ) (ha : ∃ p, Legal p q) :
    MateWithin σ 99 q := by
  have hwall : KRKWallBudget σ 95 := fun hm hb hw => wall95 hm hb hw
  exact setup_arrival_budget hwall hk ht ha

end EndgameChess.Rules.KRKCentral
