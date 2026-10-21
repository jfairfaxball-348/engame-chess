import EndgameChess.Rules.KRKHighClock.Definitions
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- At every admitted terminal, forcing is already actual named mate. -/
theorem terminal_force_iff_goal {σ : Colour} {s : State} (terminal : ¬Ongoing s) :
    F σ s ↔ G σ s := by
  constructor
  · rintro ⟨n,win⟩
    cases n with
    | zero => exact win
    | succ => exact win.resolve_right (fun branch => terminal branch.1)
  · intro goal
    exact ⟨0,goal⟩
end EndgameChess.Rules.KRKHighClock
