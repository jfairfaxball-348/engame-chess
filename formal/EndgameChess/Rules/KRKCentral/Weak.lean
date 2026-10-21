import EndgameChess.Rules.KRKCentral.Arrival
import EndgameChess.Rules.KRKSetup.WeakSafe

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK

/-- Weak-turn100 retains its forcing premise. It is a clock-free ceiling;
100 does not satisfy the strict sub100 RAW lifting premise. -/
theorem weak100 {σ : Colour} {q : Position} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn=σ.opp) (win : ForceMate σ q) :
    MateWithin σ 100 q := by
  by_cases goal : MateGoal σ q
  · exact mateWithin_mono (n := 0) goal (by omega)
  have moves : ∃ r, Legal q r := by
    by_cases actual : ∃ r, Legal q r
    · exact actual
    · exact False.elim (goal ((forceMate_no_moves_iff actual).mp win))
  have safe := krk_force_weak_safe hk ht win
  have hwall : KRKWallBudget σ 95 := fun hm hb hw => wall95 hm hb hw
  exact setup_weak_safe_budget hwall ⟨hk,ht⟩ safe moves

end EndgameChess.Rules.KRKCentral
