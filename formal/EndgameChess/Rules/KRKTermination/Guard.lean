import EndgameChess.Rules.KRKTermination.Definitions
namespace EndgameChess.Rules.KRKTermination
open RawHistoryLayer

/-- Child admission forces a live parent, even when a raw legal move exists after termination. -/
theorem step_parent_ongoing {s t : State} (step : BoardStep s t) : Ongoing s := by
  obtain ⟨m, hm, endpoint⟩ := step
  have child := t.property
  rw [endpoint] at child
  exact ((StoppedHistory.append_and_reply_lifting s.val).1 m hm |>.mp child).2
end EndgameChess.Rules.KRKTermination
