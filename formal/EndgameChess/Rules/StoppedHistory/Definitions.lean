import EndgameChess.Rules.RawAdjudication.Definitions

/-! S062 / EC-C037: strict prefixes ongoing under the chosen raw classifier. -/
namespace EndgameChess.Rules.StoppedHistory

/-- The current endpoint may be terminal; only actual strict prefixes must be ongoing.
Board-move traces contain no successful claims or procedural claim phases. -/
def Admissible {q : Position} (trace : RawTrace.Trace q) : Prop :=
  match trace with
  | .start => True
  | @RawTrace.Trace.snoc q prior _ _ =>
      Admissible prior ∧ RawAdjudication.classify ⟨q, prior⟩ = .ongoing

end EndgameChess.Rules.StoppedHistory
