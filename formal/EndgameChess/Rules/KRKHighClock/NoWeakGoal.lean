import EndgameChess.Rules.KRKHighClock.Definitions
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- An arisen exact KRK board cannot be a named mate for the lone king. -/
theorem arisen_no_weak_goal {q : Position} {σ : Colour} {sk rs wk : Square}
    (arisen : Arisen q) (material : IsKRK q σ sk rs wk) : ¬MateGoal σ.opp q := by
  intro goal
  have turn : q.turn = σ := by
    have ht := goal.1
    simpa only [opp_opp] using ht
  cases arisen with
  | refl => exact initial_not_KRK σ sk rs wk material
  | @tail p q prior legal =>
    have parentTurn : p.turn = σ.opp := by
      rw [←turn,turn_of_legal legal,opp_opp]
    have safe := legal_mover_safe legal
    rw [parentTurn] at safe
    have strongCheck : inCheck q σ = true := by simpa only [turn] using goal.2.1
    have adjacent := (inCheck_strong_krk material.1 material.2.1 material.2.2.1 material.2.2.2).mp strongCheck
    have weakCheck := (inCheck_weak_krk material.1 material.2.1 material.2.2.1 material.2.2.2).mpr
      (Or.inl (by rwa [dInf_comm] at adjacent))
    rw [weakCheck] at safe
    cases safe
end EndgameChess.Rules.KRKHighClock
