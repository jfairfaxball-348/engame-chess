import EndgameChess.Rules.RawRepetition.OccurrenceDefinitions

/-! S056 / EC-C034: raw threshold predicates, not certified FIDE adjudication. -/
namespace EndgameChess.Rules.RawClaims

/-- Raw present clock/count threshold; no lawful-history/terminal semantics. -/
def CurrentThreshold (s : RawTrace.State) : Prop :=
  100 ≤ RawClock.clock s.trace ∨ 3 ≤ RawRepetition.currentOccurrences s

/-- Quantify every actual legal intended append, retaining the real child trace. -/
def IntendedThreshold (s : RawTrace.State) : Prop :=
  ∃ m, ∃ hm : isLegal (RawTrace.erase s) m = true,
    CurrentThreshold (RawTrace.append s m hm)

/-- Raw threshold availability only, not a concrete instance of Layer.CanClaim. -/
def AvailableThreshold (s : RawTrace.State) : Prop :=
  CurrentThreshold s ∨ IntendedThreshold s

end EndgameChess.Rules.RawClaims
