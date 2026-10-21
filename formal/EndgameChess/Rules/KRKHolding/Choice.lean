import EndgameChess.Rules.KRKHolding.Saturation
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Nonforcing is preserved by every winner-turn move, and admits a safe
defensive move whenever the holder has no claim. No incoming data restriction. -/
theorem defensive_choice {σ c : Colour} {s : State} (region : Region σ s)
    (notWin : ¬F c.opp s) (ongoing : Ongoing s) :
    (((erase s).turn = c.opp) → ∀ t, BoardStep s t → ¬F c.opp t) ∧
    (((erase s).turn = c) → ¬CanClaim s → ∃ t, BoardStep s t ∧ ¬F c.opp t) := by
  classical
  constructor
  · intro turn t step ⟨n,win⟩
    exact notWin ⟨n+1,Or.inr ⟨ongoing,Or.inl ⟨turn,t,step,win⟩⟩⟩
  · intro turn noClaim
    apply Classical.byContradiction
    intro noChild
    have all : ∀ t, BoardStep s t → F c.opp t := by
      intro t edge
      apply Classical.byContradiction
      intro bad
      exact noChild ⟨t,edge,bad⟩
    obtain ⟨r,legal⟩ := ((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1
    obtain ⟨t,step,_⟩ := layer.reply_complete ongoing legal
    have decrease := (step_decreases region step).2
    cases value : fuel s with
    | zero => omega
    | succ k =>
      apply notWin
      refine ⟨k+1,Or.inr ⟨ongoing,Or.inr ⟨?_,noClaim,⟨t,step⟩,?_⟩⟩⟩
      · change (erase s).turn = c.opp.opp
        simpa only [opp_opp] using turn
      · intro u edge
        obtain ⟨next,dec⟩ := step_decreases region edge
        obtain ⟨n,win⟩ := all u edge
        exact budget_monotone.2 c.opp u _ k (by omega) (fuel_saturation u next n win)
end EndgameChess.Rules.KRKHolding
