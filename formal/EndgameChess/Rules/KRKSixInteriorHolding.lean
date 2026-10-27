import EndgameChess.Rules.KRKSixInwardCorner
import EndgameChess.Rules.KRKHighClock.StrongHold

namespace EndgameChess.Rules.KRKSixInteriorHolding
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning
set_option maxHeartbeats 500000

theorem strong_eight_interior_corner {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (inside : 0 < KRKEdgeDepth.depth wk)
    (win : MateWithin σ 8 q) : KRKSixInterior.InnerCorner wk := by
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
    have six := KRKSixGeometry.weak_seven_six next nextTurn child
    exact KRKSixInterior.weak_six_interior_corner next nextTurn
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) inside six
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

/-- Every admitted-history interior strong win at h>=92 must start at one
of the four inward-corner weak squares. All strong alternatives are covered. -/
theorem high_clock_interior_necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (turn : (erase s).turn = σ)
    (inside : 0 < KRKEdgeDepth.depth wk) (high : 92 ≤ RawClock.clock s.val.trace)
    (win : F σ s) : KRKSixInterior.InnerCorner wk := by
  have deadline := (KRKDeadline.winning_deadline material win).2
  have budget : KRKDeadline.budget σ s ≤ 8 := by simp only [KRKDeadline.budget,turn,↓reduceIte]; omega
  exact strong_eight_interior_corner material turn inside (mateWithin_mono deadline budget)

/-- Actual RAW drawing region at the next clock band, retaining arbitrary
incoming history, native flags, and all current/intended claims. -/
theorem high_clock_interior_holding {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (turn : (erase s).turn = σ)
    (inside : 0 < KRKEdgeDepth.depth wk) (high : 92 ≤ RawClock.clock s.val.trace)
    (outside : ¬KRKSixInterior.InnerCorner wk) :
    RuleHold σ s ∧ RuleHold σ.opp s ∧ ¬ActualWin σ s := by
  have noWin : ¬F σ s := fun win => outside (high_clock_interior_necessary material turn inside high win)
  have region : KRKTermination.Region σ s := Or.inl ⟨sk,rs,wk,material⟩
  refine ⟨KRKHighClock.strong_hold material,?_,?_⟩
  · apply (holding_iff_not_force region).mpr
    simpa only [opp_opp] using noWin
  · intro actual
    exact noWin ((actual_win_iff_force region).mp actual)

end EndgameChess.Rules.KRKSixInteriorHolding
