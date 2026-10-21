import EndgameChess.Rules.KRKHighClock.WeakHighClock
import EndgameChess.Rules.KRKHighClock.Terminal
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- At ongoing strong h≥98, full forcing is equivalent to an actual immediate mate. -/
theorem strong_high_clock_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 98 ≤ RawClock.clock s.val.trace) :
    F σ s ↔ ∃ t, BoardStep s t ∧ G σ t := by
  classical
  have notGoal : ¬G σ s := by
    intro goal
    exact goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
  constructor
  · rintro ⟨n,win⟩
    cases n with
    | zero => exact False.elim (notGoal win)
    | succ n =>
      rcases win with goal | ⟨_,chosen | defended⟩
      · exact False.elim (notGoal goal)
      · obtain ⟨_,t,edge,child⟩ := chosen
        have childWin : F σ t := ⟨n,child⟩
        obtain ⟨⟨ns,nr,nw,nextMaterial⟩,clock⟩ := winning_child_quiet material edge childWin
        by_cases nextOngoing : Ongoing t
        · have nextTurn : (erase t).turn = σ.opp := by
            have legal := layer.step_sound ongoing edge
            change Legal (erase s) (erase t) at legal
            rw [turn_of_legal legal,turn]
          exact False.elim ((weak_high_clock_not_force nextMaterial nextOngoing nextTurn (by omega)).1 childWin)
        · exact ⟨t,edge,(terminal_force_iff_goal nextOngoing).mp childWin⟩
      · exact False.elim (opp_ne σ (turn.symm.trans defended.1))
  · rintro ⟨t,edge,goal⟩
    exact ⟨1,Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,goal⟩⟩⟩
end EndgameChess.Rules.KRKHighClock
