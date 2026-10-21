import EndgameChess.Rules.KRKDeadline.Definitions

namespace EndgameChess.Rules.KRKDeadline
open EndgameChess.KK RawHistoryLayer KRKHolding KRKHighClock
set_option maxHeartbeats 4000000

/-- WORKING necessary deadline for the full positive-clock/history criterion.
No outcome sufficiency is inferred from its clock-free projection. -/
theorem winning_deadline {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (win : F σ s) :
    W σ (budget σ s) s ∧ MateWithin σ (budget σ s) (erase s) := by
  have saturate : ∀ n, ∀ {s : State} {sk rs wk : Square},
      IsKRK (erase s) σ sk rs wk → W σ n s → W σ (budget σ s) s := by
    intro n
    induction n with
    | zero =>
      intro s sk rs wk hk goal
      exact budget_monotone.1 σ s _ goal
    | succ n ih =>
      intro s sk rs wk hk cert
      rcases cert with goal | ⟨ongoing,chosen | defended⟩
      · exact budget_monotone.1 σ s _ goal
      · obtain ⟨turn,t,edge,child⟩ := chosen
        change (erase s).turn=σ at turn
        by_cases goal : G σ t
        · have one : W σ 1 s := Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,goal⟩⟩
          exact budget_monotone.2 σ s 1 _ (by simp only [budget,turn,↓reduceIte]; omega) one
        have childOngoing : Ongoing t := by
          cases n with
          | zero => exact False.elim (goal child)
          | succ k => exact child.resolve_left goal |>.1
        obtain ⟨⟨ns,nr,nw,next⟩,clock⟩ := winning_child_quiet hk edge ⟨n,child⟩
        have childTurn : (erase t).turn=σ.opp := by
          have ht := turn_of_legal (show Legal (erase s) (erase t) from RawTrace.raw_step_sound edge)
          change (erase t).turn=(erase s).turn.opp at ht
          simpa only [turn] using ht
        have childLow : RawClock.clock t.val.trace<99 := by
          by_cases hh : 99≤RawClock.clock t.val.trace
          · exact False.elim ((weak_high_clock_not_force next childOngoing childTurn hh).1 ⟨n,child⟩)
          · omega
        have neq : (erase t).turn≠σ := by intro he; exact opp_ne σ (he.symm.trans childTurn)
        have de : budget σ t+1=budget σ s := by
          simp only [budget,turn,neq,↓reduceIte]; omega
        rw [←de]
        exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,ih next child⟩⟩
      · obtain ⟨turn,noClaim,nonempty,all⟩ := defended
        change (erase s).turn=σ.opp at turn
        have original : F σ s := ⟨n+1,Or.inr ⟨ongoing,Or.inr ⟨turn,noClaim,nonempty,all⟩⟩⟩
        have low : RawClock.clock s.val.trace<99 := by
          by_cases hh : 99≤RawClock.clock s.val.trace
          · exact False.elim ((weak_high_clock_not_force hk ongoing turn hh).1 original)
          · omega
        have neq : (erase s).turn≠σ := by intro he; exact opp_ne σ (he.symm.trans turn)
        have de : budget σ s=(99-RawClock.clock s.val.trace)+1 := by
          simp only [budget,neq,↓reduceIte]; omega
        rw [de]
        refine Or.inr ⟨ongoing,Or.inr ⟨turn,noClaim,nonempty,?_⟩⟩
        intro t edge
        obtain ⟨⟨ns,nr,nw,next⟩,clock⟩ := winning_child_quiet hk edge ⟨n,all t edge⟩
        have childTurn : (erase t).turn=σ := by
          have ht := turn_of_legal (show Legal (erase s) (erase t) from RawTrace.raw_step_sound edge)
          change (erase t).turn=(erase s).turn.opp at ht
          simpa only [turn,opp_opp] using ht
        have childBudget : budget σ t=99-RawClock.clock s.val.trace := by
          simp only [budget,childTurn,↓reduceIte]; omega
        rw [←childBudget]
        exact ih next (all t edge)
  obtain ⟨n,cert⟩ := win
  have bounded := saturate n material cert
  exact ⟨bounded,raw_ruleMateWithin_project s σ _ bounded⟩

end EndgameChess.Rules.KRKDeadline
