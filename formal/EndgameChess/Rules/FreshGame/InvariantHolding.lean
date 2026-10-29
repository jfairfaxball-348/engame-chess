import EndgameChess.Rules.FreshGame.Holding

namespace EndgameChess.Rules.FreshGame
open EndgameChess.KK

/-- Construct an actual holding policy from a safe region: the opponent
preserves it, and the defender has a legal preserving choice whenever play continues. -/
theorem hold_of_invariant (c : Colour) (R : State → Prop)
    (safe : ∀ s, R s → ¬ MateGoal c.opp s.board)
    (opponent : ∀ s t, R s → s.board.turn ≠ c → BoardStep s t → R t)
    (own : ∀ s, R s → Ongoing s → s.board.turn = c → ∃ t, BoardStep s t ∧ R t)
    {s : State} (root : R s) : Hold c s := by
  classical
  let π : Policy := fun t =>
    if h : R t ∧ Ongoing t ∧ t.board.turn = c then
      some (Classical.choose (own t h.1 h.2.1 h.2.2))
    else defaultPolicy t
  have legal : LegalPolicy c π := by
    intro t ongoing turn
    by_cases region : R t
    · have condition : R t ∧ Ongoing t ∧ t.board.turn = c := ⟨region, ongoing, turn⟩
      simp only [π, dite_eq_left condition]
      exact (Classical.choose_spec (own t region ongoing turn)).1
    · have condition : ¬ (R t ∧ Ongoing t ∧ t.board.turn = c) := fun h => region h.1
      simpa only [π, dite_eq_right condition] using default_legal c t ongoing turn
  have preserved : ∀ {t u : State}, R t → BoardStep t u →
      (t.board.turn = c → π t = some u) → R u := by
    intro t u region step compliant
    by_cases turn : t.board.turn = c
    · have condition : R t ∧ Ongoing t ∧ t.board.turn = c := ⟨region, step.1, turn⟩
      have selected := compliant turn
      simp only [π, dite_eq_left condition, Option.some.injEq] at selected
      rw [← selected]
      exact (Classical.choose_spec (own t region step.1 turn)).2
    · exact opponent t u region turn step
  refine ⟨π, legal, ?_⟩
  intro n t path
  have region : R t := by
    induction path with
    | refl => exact root
    | @cons n a b z step compliant rest ih =>
      exact ih (preserved root step compliant)
  exact safe t region

end EndgameChess.Rules.FreshGame
