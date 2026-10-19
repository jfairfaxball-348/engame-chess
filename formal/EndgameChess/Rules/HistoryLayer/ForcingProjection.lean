import EndgameChess.Rules.HistoryLayer.Projection

/-! S033 / EC-C022: existential forcing projection, preserving its witness budget. -/
namespace EndgameChess.Rules.HistoryLayer
open EndgameChess.KK

universe u

/-- Rule-layer forcing implies frozen clock-free forcing at the erased board.
This does not instantiate a concrete FIDE history layer or prove a converse. -/
theorem ruleForceMate_project {State : Type u} (L : Layer State)
    {σ : Colour} {s : State} (h : RuleForceMate L σ s) :
    ForceMate σ (L.erase s) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, ruleMateWithin_project L hn⟩

end EndgameChess.Rules.HistoryLayer
