import EndgameChess.Rules.RawOccurrences.Definitions

/-! S042 / EC-C027: every actual append retains the complete prior key history. -/
namespace EndgameChess.Rules.RawOccurrences

/-- Query the same key in the old full history, then count the new endpoint. -/
theorem append_occurrences {K : Type u} [DecidableEq K] (key : Position → K)
    (s : RawTrace.State) (m : Move) (hm : isLegal (RawTrace.erase s) m = true) (a : K) :
    occurrences key (RawTrace.append s m hm).trace a = occurrences key s.trace a +
      (if key (play (RawTrace.erase s) m) = a then 1 else 0) := by
  unfold occurrences
  rw [(RawTrace.append_spec s m hm).2.2.1]
  by_cases hkey : key (play (RawTrace.erase s) m) = a
  · simp [List.filter_append, hkey]
  · simp [List.filter_append, hkey]

end EndgameChess.Rules.RawOccurrences
