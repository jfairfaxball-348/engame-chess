import EndgameChess.Rules.KRKTenInterior
import EndgameChess.Rules.KRKHighClock.StrongHold

namespace EndgameChess.Rules.KRKTenInteriorHolding
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning
set_option maxHeartbeats 300000

theorem strong_twelve_depth_le_one {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (win : MateWithin σ 12 q) :
    KRKEdgeDepth.depth wk ≤ 1 := by
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
    exact KRKTenInterior.weak_ten_depth_le_one next nextTurn
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) (KRKTenGeometry.weak_eleven_ten next nextTurn child)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem high_clock_depth_necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (turn : (erase s).turn = σ)
    (high : 88 ≤ RawClock.clock s.val.trace) (win : F σ s) : KRKEdgeDepth.depth wk ≤ 1 := by
  have deadline := (KRKDeadline.winning_deadline material win).2
  have budget : KRKDeadline.budget σ s ≤ 12 := by simp only [KRKDeadline.budget,turn,↓reduceIte]; omega
  exact strong_twelve_depth_le_one material turn (mateWithin_mono deadline budget)

/-- Actual RAW drawing on the deep interior, with every incoming history
and native claim branch retained, at the next strong clock threshold. -/
theorem high_clock_deep_holding {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (turn : (erase s).turn = σ)
    (high : 88 ≤ RawClock.clock s.val.trace) (deep : 2 ≤ KRKEdgeDepth.depth wk) :
    RuleHold σ s ∧ RuleHold σ.opp s ∧ ¬ActualWin σ s := by
  have noWin : ¬F σ s := by
    intro win
    have shallow := high_clock_depth_necessary material turn high win
    omega
  have region : KRKTermination.Region σ s := Or.inl ⟨sk,rs,wk,material⟩
  refine ⟨KRKHighClock.strong_hold material,?_,?_⟩
  · apply (holding_iff_not_force region).mpr
    simpa only [opp_opp] using noWin
  · intro actual
    exact noWin ((actual_win_iff_force region).mp actual)

end EndgameChess.Rules.KRKTenInteriorHolding
