import EndgameChess.Rules.RawClock.Append
namespace EndgameChess.Rules.RawClock

/-- A board ply increases the raw counter by at most one. -/
theorem append_clock_le (s : RawTrace.State) (m : Move)
    (hm : isLegal (RawTrace.erase s) m = true) :
    clock (RawTrace.append s m hm).trace ≤ clock s.trace + 1 := by
  rw [append_clock]
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

end EndgameChess.Rules.RawClock
