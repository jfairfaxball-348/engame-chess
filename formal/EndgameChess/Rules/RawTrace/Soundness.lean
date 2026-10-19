import EndgameChess.Rules.RawTrace.Definitions

/-! S035 / EC-C023: every actual trace append projects to kernel legality. -/
namespace EndgameChess.Rules.RawTrace

theorem raw_step_sound {s t : State} (h : RawBoardStep s t) :
    Legal (erase s) (erase t) := by
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨m, hm, rfl⟩

end EndgameChess.Rules.RawTrace
