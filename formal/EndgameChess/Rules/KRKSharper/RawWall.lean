import EndgameChess.Rules.KRKSharper.AxisWall
import EndgameChess.Rules.KRKHistory.Lifting
namespace EndgameChess.Rules.RawHistoryLayer
open EndgameChess.KK

/-- Partial RAW wall family in any proved frame, with the ORIGINAL incoming history. -/
theorem raw_axis_rank_six_wall_ruleMateWithin_sharper (s : State) (σ : Colour) (g : BoardSym)
    {sk rs wk : Square} (hq : Matches (erase s) σ ⟨sk, rs, wk, true⟩)
    (below : (g.f sk).2.val < (g.f rs).2.val)
    (above : (g.f rs).2.val < (g.f wk).2.val) (rankSix : (g.f rs).2.val = 6)
    (clockBudget : RawClock.clock s.val.trace + 73 < 100)
    (rootCount : RawRepetition.currentOccurrences s.val < 3)
    (hist : LowerRankHistory σ s.val) : HistoryLayer.RuleMateWithin layer σ 73 s := by
  have clockFree := krk_axis_wall_bound_sharper g hq below above
  have budget : 73 * (7 - (g.f rs).2.val) = 73 := by omega
  rw [budget] at clockFree
  exact raw_ruleMateWithin_of_strategy_history s σ 73 clockFree clockBudget rootCount hist
end EndgameChess.Rules.RawHistoryLayer
