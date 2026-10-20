import EndgameChess.Rules.RawHistoryLayer.Definitions
import EndgameChess.Rules.RawTrace.Prepend
import EndgameChess.Rules.RawClock.StepBound

/-! S066 / EC-C039: sufficient explicit clock and full-prefix repetition bounds. -/
namespace EndgameChess.Rules.RawHistoryLayer

open EndgameChess.KK

/-- Same-budget lifting under a strong certificate over ALL actual raw prefixes.
The certificate is sufficient only, not a claim that every KRK history has it. -/
theorem raw_ruleMateWithin_of_budget (s : State) (σ : Colour) (n : Nat)
    (clockBudget : RawClock.clock s.val.trace + n < 100)
    (repetitionBudget : ∀ {k : Nat} {t : RawTrace.State}, k ≤ n →
      RawTrace.Extends k s.val t → RawRepetition.currentOccurrences t < 3)
    (winning : MateWithin σ n (erase s)) :
    HistoryLayer.RuleMateWithin layer σ n s := by
  induction n generalizing s with
  | zero => exact winning
  | succ n ih =>
    rcases winning with goal | ⟨nondead, turns⟩
    · exact Or.inl goal
    have rootCount : RawRepetition.currentOccurrences s.val < 3 :=
      repetitionBudget (Nat.zero_le _) (RawTrace.Extends.refl s.val)
    have moves : ∃ r, Legal (erase s) r := by
      rcases turns with ⟨_, r, legal, _⟩ | ⟨_, replies, _⟩
      · exact ⟨r, legal⟩
      · exact replies
    have ongoing : Ongoing s := (RawAdjudication.ongoing_iff s.val).mpr
      ⟨nondead, moves, by omega, by omega⟩
    have noClaim : ¬CanClaim s := by
      intro available
      rcases available with current | ⟨m, hm, current⟩
      · rcases current with clock | count <;> omega
      · have childClock := RawClock.append_clock_le s.val m hm
        have childCount := repetitionBudget (show 1 ≤ n + 1 by omega)
          (RawTrace.Extends.snoc (RawTrace.Extends.refl s.val) ⟨m, hm, rfl⟩)
        rcases current with clock | count <;> omega
    have descend : ∀ t : State, BoardStep s t →
        RawClock.clock t.val.trace + n < 100 ∧
        (∀ {k : Nat} {u : RawTrace.State}, k ≤ n →
          RawTrace.Extends k t.val u → RawRepetition.currentOccurrences u < 3) := by
      intro t step
      obtain ⟨m, hm, endpoint⟩ := step
      have childClock : RawClock.clock t.val.trace ≤ RawClock.clock s.val.trace + 1 := by
        rw [endpoint]
        exact RawClock.append_clock_le s.val m hm
      refine ⟨by omega, ?_⟩
      intro k u depth path
      exact repetitionBudget (by omega)
        (RawTrace.extends_prepend ⟨m, hm, endpoint⟩ path)
    refine Or.inr ⟨ongoing, ?_⟩
    rcases turns with ⟨whose, r, legal, win⟩ | ⟨whose, replies, all⟩
    · obtain ⟨m, hm, rfl⟩ := legal
      have admitted := ((StoppedHistory.append_and_reply_lifting s.val).1 m hm).mpr
        ⟨s.property, ongoing⟩
      let t : State := ⟨RawTrace.append s.val m hm, admitted⟩
      have step : BoardStep s t := ⟨m, hm, rfl⟩
      obtain ⟨childClock, childCount⟩ := descend t step
      exact Or.inl ⟨whose, t, step, ih t childClock childCount win⟩
    · have someStep : ∃ t, BoardStep s t := by
        obtain ⟨r, legal⟩ := replies
        obtain ⟨t, step, _⟩ := layer.reply_complete ongoing legal
        exact ⟨t, step⟩
      refine Or.inr ⟨whose, noClaim, someStep, ?_⟩
      intro t step
      have legal := RawTrace.raw_step_sound step
      obtain ⟨childClock, childCount⟩ := descend t step
      exact ih t childClock childCount (all (erase t) legal)

end EndgameChess.Rules.RawHistoryLayer
