import EndgameChess.Rules.RawRepetition.OccurrenceDefinitions
import EndgameChess.Rules.RawOccurrences.Append

/-! S054 / EC-C033: old full history is queried at the NEW current key. -/
namespace EndgameChess.Rules.RawRepetition

/-- Current count after actual append queries the new endpoint in the old full history. -/
theorem append_currentOccurrences (s : RawTrace.State) (m : Move)
    (hm : isLegal (RawTrace.erase s) m = true) :
    currentOccurrences (RawTrace.append s m hm) =
      occurrences s.trace (play (RawTrace.erase s) m) + 1 := by
  classical
  unfold currentOccurrences
  change occurrences (RawTrace.append s m hm).trace (play (RawTrace.erase s) m) = _
  unfold occurrences
  rw [RawOccurrences.append_occurrences]
  simp

end EndgameChess.Rules.RawRepetition
