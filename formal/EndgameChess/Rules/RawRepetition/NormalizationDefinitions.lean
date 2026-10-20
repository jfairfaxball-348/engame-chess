import EndgameChess.Rules.RawRepetition.Definitions

/-! S050 / EC-C031: additive effective-ep normalized raw position. -/
namespace EndgameChess.Rules.RawRepetition

/-- Keep exactly the effective target; no lawful-history assertion. -/
noncomputable def normalizeEP (q : Position) : Position :=
  {q with ep := effectiveEP q}

end EndgameChess.Rules.RawRepetition
