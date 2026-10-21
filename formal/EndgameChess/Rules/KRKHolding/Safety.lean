import EndgameChess.Rules.KRKHolding.Policy
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Full nonforcing produces an actual legal policy safe on EVERY compliant prefix. -/
theorem hold_of_not_force {σ c : Colour} {s : State} (region : Region σ s)
    (notWin : ¬F c.opp s) : RuleHold c s := by
  classical
  obtain ⟨π,legal,preserve⟩ := holding_policy σ c
  refine ⟨π,legal,?_⟩
  have invariant : ∀ {n s t}, PolicyPath c π n s t →
      Region σ s → ¬F c.opp s → ¬F c.opp t := by
    intro n root t path
    induction path with
    | refl => intro _ h; exact h
    | @cons n root u t edge choice tail ih =>
      intro rootRegion rootNotWin
      have next := (step_decreases rootRegion edge).1
      have ongoing := step_parent_ongoing edge
      have childNotWin : ¬F c.opp u := by
        rcases colour_cases c (erase root).turn with turn | turn
        · exact preserve root u rootRegion rootNotWin ongoing turn (choice turn)
        · exact (defensive_choice rootRegion rootNotWin ongoing).1 turn u edge
      exact ih next childNotWin
  intro n t path goal
  exact invariant path region notWin ⟨0,goal⟩
end EndgameChess.Rules.KRKHolding
