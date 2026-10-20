import EndgameChess.Rules.KRKHistory.Lifting
import EndgameChess.Rules.KRKBound.Wall
namespace EndgameChess.Rules.RawHistoryLayer
open EndgameChess.KK

/-- A partial actual-history RAW winning family, using the useful 84-ply coordinate bound. -/
theorem raw_rank_six_wall_ruleMateWithin (s : State) (σ : Colour) {sk rs wk : Square}
    (hq : Matches (erase s) σ ⟨sk, rs, wk, true⟩)
    (below : sk.2.val < rs.2.val) (above : rs.2.val < wk.2.val) (rankSix : rs.2.val = 6)
    (clockBudget : RawClock.clock s.val.trace + 84 < 100)
    (rootCount : RawRepetition.currentOccurrences s.val < 3)
    (hist : LowerRankHistory σ s.val) :
    HistoryLayer.RuleMateWithin layer σ 84 s := by
  have clockFree := krk_rank_wall_bound hq below above
  have budget : 84 * (7 - rs.2.val) = 84 := by omega
  rw [budget] at clockFree
  exact raw_ruleMateWithin_of_strategy_history s σ 84 clockFree clockBudget rootCount hist
end EndgameChess.Rules.RawHistoryLayer
