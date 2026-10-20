import EndgameChess.Rules.KRKSetup.NotCheck
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000

/-- Any exact strong-turn KRK produced by a kernel-legal move forces mate,
for either colour and arbitrary flags. No history-aware or exact-distance claim. -/
theorem setup_arrival_budget {q : Position} {σ : Colour} {sk rs wk : Square}
    (hwall : KRKWallBudget σ B)
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (ha : ∃ p, Legal p q) : MateWithin σ (B + 4) q := by
  obtain ⟨p, hl⟩ := ha
  have hp : p.turn = σ.opp := by rw [← ht, turn_of_legal hl, opp_opp]
  have hc := legal_mover_safe hl
  rw [hp] at hc
  exact setup_strong_budget_of_not_check hwall hk ht hc
end EndgameChess.Rules
