import EndgameChess.Rules.KRKFresh.ClockZeroCounts
import EndgameChess.Rules.KRKFresh.Lifting
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning

/-- Every supplied sub100 clock-free KRK certificate lifts at clock0 with NO incoming premise. -/
theorem clock_zero_sub100 (s : State) (σ : Colour) (n : Nat)
    (material : Query σ (erase s)) (zero : RawClock.clock s.val.trace = 0)
    (winning : MateWithin σ n (erase s)) (small : n < 100) : W σ n s ∧ ActualWin σ s := by
  have nondead := forceMate_not_dead (show ForceMate σ (erase s) from ⟨n,winning⟩)
  have counts := clock_zero_counts s σ zero nondead
  have rootCount : RawRepetition.currentOccurrences s.val < 3 := by
    have count := counts (erase s) material
    change RawRepetition.occurrences s.val.trace (erase s) < 3
    omega
  have hist : History σ s.val := by
    intro r query _ _
    have count := counts r query
    omega
  have raw := restricted_lifting s σ n material winning (by omega) rootCount hist
  exact ⟨raw,actual_win_of_force (Or.inl material) ⟨n,raw⟩⟩
end EndgameChess.Rules.KRKFresh
