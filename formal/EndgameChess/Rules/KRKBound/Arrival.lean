import EndgameChess.Rules.KRKBound.NotCheck
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

/-- Any exact strong-turn KRK produced by a kernel-legal move forces mate,
for either colour and arbitrary flags. No clock/repetition or distance claim. -/
theorem krk_strong_arrival_bound {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (ha : ∃ p, Legal p q) : MateWithin σ 508 q := by
  obtain ⟨p, hl⟩ := ha
  have hp : p.turn = σ.opp := by rw [← ht, turn_of_legal hl, opp_opp]
  have hc := legal_mover_safe hl
  rw [hp] at hc
  exact krk_strong_bound_of_not_check hk ht hc
end EndgameChess.Rules
