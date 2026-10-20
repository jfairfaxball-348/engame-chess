import EndgameChess.Rules.KRKTermination.Guard
namespace EndgameChess.Rules.KRKTermination
open RawHistoryLayer

/-- An admitted endpoint has no board continuation exactly when it is terminal. -/
theorem maximal_iff_terminal (s : State) : Maximal s ↔ ¬Ongoing s := by
  constructor
  · intro maximal ongoing
    obtain ⟨r, legal⟩ := ((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1
    obtain ⟨t, step, _⟩ := layer.reply_complete ongoing legal
    exact maximal ⟨t, step⟩
  · intro terminal ⟨t, step⟩
    exact terminal (step_parent_ongoing step)
end EndgameChess.Rules.KRKTermination
