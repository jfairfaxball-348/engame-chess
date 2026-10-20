import EndgameChess.Rules.RawRepetition.KeyDefinitions
import EndgameChess.Rules.RawOccurrences.Definitions

/-! S054 / EC-C033: concrete full normalized-key counts in stored raw history. -/
namespace EndgameChess.Rules.RawRepetition

/-- Query a full normalized key in every stored endpoint, with local classical equality. -/
noncomputable def occurrences {q : Position} (t : RawTrace.Trace q) (a : Position) : Nat := by
  classical
  exact RawOccurrences.occurrences key t (key a)

/-- Include the current endpoint itself in its full-history occurrence count. -/
noncomputable def currentOccurrences (s : RawTrace.State) : Nat :=
  occurrences s.trace (RawTrace.erase s)

end EndgameChess.Rules.RawRepetition
