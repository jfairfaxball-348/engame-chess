import EndgameChess.Rules.RawTrace.Append

/-! S042 / EC-C027: generic fixed keys, not FIDE repetition-key correctness. -/
namespace EndgameChess.Rules.RawOccurrences

/-- Count queried keys in ALL stored endpoints, including initial and current. -/
def occurrences {K : Type u} [DecidableEq K] (key : Position → K)
    {q : Position} (t : RawTrace.Trace q) (a : K) : Nat :=
  (t.positions.filter (fun p => decide (key p = a))).length

end EndgameChess.Rules.RawOccurrences
