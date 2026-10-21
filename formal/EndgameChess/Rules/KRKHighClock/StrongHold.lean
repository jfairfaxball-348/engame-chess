import EndgameChess.Rules.KRKHighClock.GoodGoal
import EndgameChess.Rules.KRKHighClock.Material
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- Strong nonloss for every admitted exact KRK history, with no incoming restriction. -/
theorem strong_hold {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) : RuleHold σ s := by
  obtain ⟨π,legal,_⟩ := holding_policy σ σ
  refine ⟨π,legal,?_⟩
  have invariant : ∀ {n root t}, PolicyPath σ π n root t → Good σ root → Good σ t := by
    intro n root t path
    induction path with
    | refl => intro h; exact h
    | cons edge _ _ ih => intro h; exact ih (good_step h edge)
  intro n t path
  exact good_no_weak_goal (invariant path (Or.inl ⟨sk,rs,wk,material⟩))
end EndgameChess.Rules.KRKHighClock
