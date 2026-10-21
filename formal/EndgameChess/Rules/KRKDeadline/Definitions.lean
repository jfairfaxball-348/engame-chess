import EndgameChess.Rules.KRKHighClock.WeakHighClock

namespace EndgameChess.Rules.KRKDeadline
open EndgameChess.KK RawHistoryLayer

/-- Exact optional-claim deadline, including the strong immediate-mate exception. -/
def budget (σ : Colour) (s : State) : Nat :=
  if (erase s).turn=σ then max 1 (100-RawClock.clock s.val.trace)
  else 100-RawClock.clock s.val.trace

end EndgameChess.Rules.KRKDeadline
