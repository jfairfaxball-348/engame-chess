import EndgameChess.Rules.RawClock.Definitions
namespace EndgameChess.Rules.RawClock

/-- Structural induction on full stored history; units are board plies. -/
theorem clock_le_length {q : Position} (t : RawTrace.Trace q) :
    clock t ≤ t.moves.length := by
  induction t with
  | start => exact Nat.le_refl 0
  | @snoc q prior m hm ih =>
    simp only [clock, RawTrace.Trace.moves, List.length_append, List.length_singleton]
    split
    · exact Nat.zero_le _
    · exact Nat.add_le_add_right ih 1

end EndgameChess.Rules.RawClock
