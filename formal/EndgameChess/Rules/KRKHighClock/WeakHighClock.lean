import EndgameChess.Rules.KRKHighClock.WinningChild
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- At an ongoing lone turn with h≥99, actual capture/claim defences exclude strong forcing. -/
theorem weak_high_clock_not_force {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 99 ≤ RawClock.clock s.val.trace) :
    ¬F σ s ∧ RuleHold σ.opp s := by
  have notWin : ¬F σ s := by
    rintro ⟨n,win⟩
    have notGoal : ¬G σ s := by
      intro goal
      exact goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
    cases n with
    | zero => exact notGoal win
    | succ n =>
      rcases win with goal | ⟨_,chosen | defended⟩
      · exact notGoal goal
      · exact opp_ne σ (chosen.1.symm.trans turn)
      · obtain ⟨_,noClaim,⟨t,edge⟩,all⟩ := defended
        have nextClock := (winning_child_quiet material edge ⟨n,all t edge⟩).2
        obtain ⟨m,hm,endpoint⟩ := edge
        have intended : RawClaims.IntendedThreshold s.val := by
          refine ⟨m,hm,Or.inl ?_⟩
          rw [←endpoint]
          omega
        exact noClaim (Or.inr intended)
  refine ⟨notWin,?_⟩
  apply hold_of_not_force (σ := σ) (c := σ.opp) (Or.inl ⟨sk,rs,wk,material⟩)
  simpa only [opp_opp] using notWin
end EndgameChess.Rules.KRKHighClock
