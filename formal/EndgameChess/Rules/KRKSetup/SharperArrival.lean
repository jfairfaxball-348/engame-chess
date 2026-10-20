import EndgameChess.Rules.KRKSetup.Arrival
import EndgameChess.Rules.KRKSetup.UniformWall
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000


/-- Actual setup composition improves the global clock-free strong-arrival ceiling. -/
theorem krk_strong_arrival_bound_442 {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (ha : ∃ p, Legal p q) :
    MateWithin σ 442 q := by
  exact setup_arrival_budget (krk_wall_uniform_438 σ) hk ht ha

end EndgameChess.Rules
