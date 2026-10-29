import EndgameChess.Rules.KRKTenSecondCorner

namespace EndgameChess.Rules.KRKTenSecondCornerHolding
open EndgameChess.KK KRKNativeFrame RawHistoryLayer KRKHolding KRKWinning
set_option maxHeartbeats 300000

theorem strong_no_twelve (g : Frame) {q : Position} {σ : Colour} {sk rs wk : Square}
    (target : g.f wk = ((2 : Fin 8),2)) (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (inside : 0 < KRKEdgeDepth.depth wk) : ¬MateWithin σ 12 q := by
  intro win
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
    exact KRKTenSecondCorner.framed_kernel_no_ten g target next nextTurn
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) inside (KRKTenGeometry.weak_eleven_ten next nextTurn child)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem high_clock_holding (g : Frame) {s : State} {σ : Colour} {sk rs wk : Square}
    (target : g.f wk = ((2 : Fin 8),2)) (material : IsKRK (erase s) σ sk rs wk)
    (turn : (erase s).turn = σ) (inside : 0 < KRKEdgeDepth.depth wk)
    (high : 88 ≤ RawClock.clock s.val.trace) :
    RuleHold σ s ∧ RuleHold σ.opp s ∧ ¬ActualWin σ s := by
  have noWin : ¬F σ s := by
    intro win
    have deadline := (KRKDeadline.winning_deadline material win).2
    have budget : KRKDeadline.budget σ s ≤ 12 := by simp only [KRKDeadline.budget,turn,↓reduceIte]; omega
    exact strong_no_twelve g target material turn inside (mateWithin_mono deadline budget)
  have region : KRKTermination.Region σ s := Or.inl ⟨sk,rs,wk,material⟩
  refine ⟨KRKHighClock.strong_hold material,?_,?_⟩
  · apply (holding_iff_not_force region).mpr
    simpa only [opp_opp] using noWin
  · intro actual
    exact noWin ((actual_win_iff_force region).mp actual)

end EndgameChess.Rules.KRKTenSecondCornerHolding
