import EndgameChess.Rules.RawClaims.Definitions
import EndgameChess.Rules.RawClock.StepBound
import EndgameChess.Rules.RawRepetition.CurrentAppend

/-! S056 / EC-C034: explicit budgets exclude current and every intended threshold. -/
namespace EndgameChess.Rules.RawClaims

/-- No raw threshold when root and every actual legal intended child have room. -/
theorem no_threshold_certificate (s : RawTrace.State)
    (budget : RawClock.clock s.trace + 1 < 100)
    (current : RawRepetition.currentOccurrences s < 3)
    (queries : ∀ m, ∀ _hm : isLegal (RawTrace.erase s) m = true,
      RawRepetition.occurrences s.trace (play (RawTrace.erase s) m) < 2) :
    ¬AvailableThreshold s := by
  have root : ¬CurrentThreshold s := by
    intro h
    rcases h with clock | count <;> omega
  intro available
  rcases available with present | intended
  · exact root present
  · obtain ⟨m, hm, threshold⟩ := intended
    have childClock := RawClock.append_clock_le s m hm
    have childCount := RawRepetition.append_currentOccurrences s m hm
    have query := queries m hm
    rcases threshold with clock | count <;> omega

end EndgameChess.Rules.RawClaims
