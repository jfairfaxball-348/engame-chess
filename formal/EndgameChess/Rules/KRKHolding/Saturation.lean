import EndgameChess.Rules.KRKHolding.Monotone
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Every finite rule-win certificate saturates at the universal KRK fuel. -/
theorem fuel_saturation {σ c : Colour} (s : State) (region : Region σ s) :
    ∀ n, W c n s → W c (fuel s) s := by
  generalize value : fuel s = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    intro n win
    cases n with
    | zero => exact budget_monotone.1 c s _ win
    | succ n =>
      rcases win with goal | ⟨ongoing, chosen | defended⟩
      · exact budget_monotone.1 c s _ goal
      · obtain ⟨turn,t,step,child⟩ := chosen
        obtain ⟨next,dec⟩ := step_decreases region step
        have smaller : fuel t < k := by omega
        have certified := ih (fuel t) smaller t next rfl n child
        cases k with
        | zero => omega
        | succ k =>
          exact Or.inr ⟨ongoing, Or.inl ⟨turn,t,step,
            budget_monotone.2 c t _ k (by omega) certified⟩⟩
      · obtain ⟨turn,noClaim,nonempty,all⟩ := defended
        obtain ⟨t,step⟩ := nonempty
        have dec := (step_decreases region step).2
        cases k with
        | zero => omega
        | succ k =>
          refine Or.inr ⟨ongoing, Or.inr ⟨turn,noClaim,⟨t,step⟩,?_⟩⟩
          intro u edge
          obtain ⟨next,decu⟩ := step_decreases region edge
          have certified := ih (fuel u) (by omega) u next rfl n (all u edge)
          exact budget_monotone.2 c u _ k (by omega) certified
end EndgameChess.Rules.KRKHolding
