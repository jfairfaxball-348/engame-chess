import EndgameChess.Rules.RawClaims.Definitions
import EndgameChess.Rules.RawRepetition.CurrentAppend

/-! S058 / EC-C035: exact current/intended raw threshold complement. -/
namespace EndgameChess.Rules.RawClaims

/-- Exact root and ALL legal-child conditions for absence of raw thresholds. -/
theorem no_threshold_iff (s : RawTrace.State) :
    ¬AvailableThreshold s ↔
      RawClock.clock s.trace < 100 ∧ RawRepetition.currentOccurrences s < 3 ∧
      (∀ m, ∀ hm : isLegal (RawTrace.erase s) m = true,
        RawClock.clock (RawTrace.append s m hm).trace < 100 ∧
        RawRepetition.occurrences s.trace (play (RawTrace.erase s) m) < 2) := by
  constructor
  · intro absent
    have root : ¬CurrentThreshold s := fun h => absent (Or.inl h)
    have rootClock : RawClock.clock s.trace < 100 := by
      apply Nat.lt_of_not_ge
      intro h
      exact root (Or.inl (by omega))
    have rootCount : RawRepetition.currentOccurrences s < 3 := by
      apply Nat.lt_of_not_ge
      intro h
      exact root (Or.inr (by omega))
    refine ⟨rootClock, rootCount, ?_⟩
    intro m hm
    have child : ¬CurrentThreshold (RawTrace.append s m hm) :=
      fun h => absent (Or.inr ⟨m, hm, h⟩)
    have childClock : RawClock.clock (RawTrace.append s m hm).trace < 100 := by
      apply Nat.lt_of_not_ge
      intro h
      exact child (Or.inl (by omega))
    have childCount : RawRepetition.currentOccurrences (RawTrace.append s m hm) < 3 := by
      apply Nat.lt_of_not_ge
      intro h
      exact child (Or.inr (by omega))
    have update := RawRepetition.append_currentOccurrences s m hm
    exact ⟨childClock, by omega⟩
  · rintro ⟨rootClock, rootCount, children⟩ available
    rcases available with present | intended
    · rcases present with clock | count <;> omega
    · obtain ⟨m, hm, threshold⟩ := intended
      obtain ⟨childClock, query⟩ := children m hm
      have update := RawRepetition.append_currentOccurrences s m hm
      rcases threshold with clock | count <;> omega

end EndgameChess.Rules.RawClaims
