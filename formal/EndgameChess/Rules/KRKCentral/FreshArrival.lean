import EndgameChess.Rules.KRKCentral.Weak
import EndgameChess.Rules.KRKFresh.FreshLift

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning

/-- Actual RAW clock-zero win at every strong KRK legal arrival, without
incoming repetition-count assumptions. Both colours and all weak replies. -/
theorem fresh_arrival99 (s : State) (σ : Colour) {sk rs wk : Square}
    (hk : IsKRK (erase s) σ sk rs wk) (ht : (erase s).turn=σ)
    (ha : ∃ p, Legal p (erase s)) (zero : RawClock.clock s.val.trace=0) :
    W σ 99 s ∧ ActualWin σ s := by
  exact KRKFresh.clock_zero_sub100 s σ 99 ⟨sk,rs,wk,hk⟩ zero
    (arrival99 hk ht ha) (by decide)

end EndgameChess.Rules.KRKCentral
