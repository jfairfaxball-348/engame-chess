import EndgameChess.Rules.KRKFresh.FreshLift
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning

/-- Framed rank-six RAW wall at clock0: W73 and actual win, no incoming histogram/count. -/
theorem clock_zero_axis_wall (s : State) (σ : Colour) (g : BoardSym) {sk rs wk : Square}
    (hq : Matches (erase s) σ ⟨sk,rs,wk,true⟩)
    (below : (g.f sk).2.val < (g.f rs).2.val) (above : (g.f rs).2.val < (g.f wk).2.val)
    (rankSix : (g.f rs).2.val = 6) (zero : RawClock.clock s.val.trace = 0) :
    W σ 73 s ∧ ActualWin σ s := by
  have clockFree := krk_axis_wall_bound_sharper g hq below above
  have budget : 73 * (7 - (g.f rs).2.val) = 73 := by omega
  rw [budget] at clockFree
  exact clock_zero_sub100 s σ 73 ⟨sk,rs,wk,hq.1⟩ zero clockFree (by decide)
end EndgameChess.Rules.KRKFresh
