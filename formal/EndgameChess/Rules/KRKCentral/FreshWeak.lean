import EndgameChess.Rules.KRKCentral.FreshArrival

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning

/-- The integrated two-ply saving puts the weak-turn clock0 domain below100. -/
theorem fresh_weak98 (s : State) (σ : Colour) {sk rs wk : Square}
    (hk : IsKRK (erase s) σ sk rs wk) (ht : (erase s).turn=σ.opp)
    (win : ForceMate σ (erase s)) (zero : RawClock.clock s.val.trace=0) :
    W σ 98 s ∧ ActualWin σ s := by
  exact KRKFresh.clock_zero_sub100 s σ 98 ⟨sk,rs,wk,hk⟩ zero
    (weak98 hk ht win) (by decide)

end EndgameChess.Rules.KRKCentral
