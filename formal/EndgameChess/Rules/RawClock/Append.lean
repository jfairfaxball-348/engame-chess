import EndgameChess.Rules.RawClock.Definitions
namespace EndgameChess.Rules.RawClock

/-- Exact update on EVERY raw legal append; no ongoing guard. -/
theorem append_clock (s : RawTrace.State) (m : Move)
    (hm : isLegal (RawTrace.erase s) m = true) :
    clock (RawTrace.append s m hm).trace =
      if zeroing (RawTrace.erase s) m then 0 else clock s.trace + 1 := rfl

end EndgameChess.Rules.RawClock
