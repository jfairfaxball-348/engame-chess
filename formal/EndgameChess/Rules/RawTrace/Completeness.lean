import EndgameChess.Rules.RawTrace.Definitions

/-! S035 / EC-C023: complete lifting, retaining every raw legal reply. -/
namespace EndgameChess.Rules.RawTrace

theorem raw_step_complete (s : State) {r : Position} (h : Legal (erase s) r) :
    ∃ t, RawBoardStep s t ∧ erase t = r := by
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨append s m hm, ⟨m, hm, rfl⟩, rfl⟩

end EndgameChess.Rules.RawTrace
