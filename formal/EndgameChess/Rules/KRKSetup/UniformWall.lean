import EndgameChess.Rules.KRKSetup.Definitions
import EndgameChess.Rules.KRKSharper.Wall
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000


/-- Concrete hypothesis is proved from the sharper coordinate theorem, not postulated. -/
theorem krk_wall_uniform_438 (σ : Colour) : KRKWallBudget σ 438 := by
  intro q sk rs wk hq hb hw
  exact mateWithin_mono (krk_rank_wall_bound_sharper hq hb hw) (by omega)

end EndgameChess.Rules
