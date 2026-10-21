import EndgameChess.Rules.KRKHolding.Definitions
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer

/-- Goal at every budget, and monotonicity for the actual frozen rule recurrence. -/
theorem budget_monotone :
    (∀ (c : Colour) (s : State) (n : Nat), G c s → W c n s) ∧
    (∀ (c : Colour) (s : State) (n m : Nat), n ≤ m → W c n s → W c m s) := by
  have goal : ∀ (c : Colour) (s : State) (n : Nat), G c s → W c n s := by
    intro c s n h
    cases n with
    | zero => exact h
    | succ => exact Or.inl h
  have step : ∀ (c : Colour) (n : Nat) (s : State), W c n s → W c (n+1) s := by
    intro c n
    induction n with
    | zero => intro s h; exact Or.inl h
    | succ n ih =>
      intro s h
      rcases h with hg | ⟨ho, hc | hd⟩
      · exact Or.inl hg
      · obtain ⟨ht,t,hs,hw⟩ := hc
        exact Or.inr ⟨ho, Or.inl ⟨ht,t,hs,ih t hw⟩⟩
      · obtain ⟨ht,hn,hne,hall⟩ := hd
        exact Or.inr ⟨ho, Or.inr ⟨ht,hn,hne,fun t hs => ih t (hall t hs)⟩⟩
  refine ⟨goal, ?_⟩
  intro c s n m le h
  induction le with
  | refl => exact h
  | step _ ih => exact step c _ s ih
end EndgameChess.Rules.KRKHolding
