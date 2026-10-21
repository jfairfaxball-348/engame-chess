import EndgameChess.Rules.KRKHighClock.NoWeakGoal
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- Every actual KRK-or-dead endpoint excludes weak named mate. -/
theorem good_no_weak_goal {σ : Colour} {s : State} (good : Good σ s) : ¬G σ.opp s := by
  intro goal
  rcases good with ⟨sk,rs,wk,material⟩ | dead
  · exact arisen_no_weak_goal (RawTrace.trace_arisen s.val.trace) material goal
  · exact dead ⟨erase s,.refl _,goal.2⟩
end EndgameChess.Rules.KRKHighClock
