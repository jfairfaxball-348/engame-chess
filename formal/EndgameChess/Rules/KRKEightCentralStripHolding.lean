import EndgameChess.Rules.KRKEightCentralStrip
import EndgameChess.Rules.KRKHighClock.StrongHold

namespace EndgameChess.Rules.KRKEightCentralStripHolding
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning
set_option maxHeartbeats 300000

theorem strong_no_ten {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (middle : KRKEightCentralStrip.MiddleStrip wk) : ¬MateWithin σ 10 q := by
  intro win
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
    exact KRKEightCentralStrip.middle_kernel_no_eight next nextTurn middle
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) (KRKEightGeometry.weak_nine_eight next nextTurn child)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

/-- Both-player holding for all incoming RAW histories on the eight middle
strip squares at the strong clock threshold ninety. -/
theorem high_clock_holding {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (turn : (erase s).turn = σ)
    (high : 90 ≤ RawClock.clock s.val.trace) (middle : KRKEightCentralStrip.MiddleStrip wk) :
    RuleHold σ s ∧ RuleHold σ.opp s ∧ ¬ActualWin σ s := by
  have noWin : ¬F σ s := by
    intro win
    have deadline := (KRKDeadline.winning_deadline material win).2
    have budget : KRKDeadline.budget σ s ≤ 10 := by simp only [KRKDeadline.budget,turn,↓reduceIte]; omega
    exact strong_no_ten material turn middle (mateWithin_mono deadline budget)
  have region : KRKTermination.Region σ s := Or.inl ⟨sk,rs,wk,material⟩
  refine ⟨KRKHighClock.strong_hold material,?_,?_⟩
  · apply (holding_iff_not_force region).mpr
    simpa only [opp_opp] using noWin
  · intro actual
    exact noWin ((actual_win_iff_force region).mp actual)

end EndgameChess.Rules.KRKEightCentralStripHolding
