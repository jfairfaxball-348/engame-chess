import EndgameChess.Rules.KRKSetup.WeakSafe
import EndgameChess.Rules.KRKSetup.UniformWall
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000


/-- This weak-turn ceiling retains its forcing premise; it does not assert every input wins. -/
theorem krk_weak_forcing_bound_443 {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp) (win : ForceMate σ q) :
    MateWithin σ 443 q := by
  by_cases goal : MateGoal σ q
  · exact mateWithin_mono (n := 0) goal (by omega)
  have moves : ∃ r, Legal q r := by
    by_cases actual : ∃ r, Legal q r
    · exact actual
    · exact False.elim (goal ((forceMate_no_moves_iff actual).mp win))
  have safe := krk_force_weak_safe hk ht win
  exact setup_weak_safe_budget (krk_wall_uniform_438 σ) ⟨hk, ht⟩ safe moves

end EndgameChess.Rules
