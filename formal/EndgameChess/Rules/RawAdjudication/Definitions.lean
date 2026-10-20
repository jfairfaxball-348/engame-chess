import EndgameChess.Rules.RawRepetition.OccurrenceDefinitions

/-! S060 / EC-C036: raw mate-first endpoint status, not lawful-history adjudication. -/
namespace EndgameChess.Rules.RawAdjudication

open EndgameChess.KK

/-- No check and no legal successor at the raw endpoint. -/
def Stalemated (q : Position) : Prop :=
  inCheck q q.turn = false ∧ ¬∃ r, Legal q r

/-- Draw triggers before adding lawful-history and rules correspondence proofs. -/
def DrawTrigger (s : RawTrace.State) : Prop :=
  Stalemated (RawTrace.erase s) ∨ DeadK (RawTrace.erase s) ∨
    150 ≤ RawClock.clock s.trace ∨ 5 ≤ RawRepetition.currentOccurrences s

inductive EndpointStatus
  | mate (winner : Colour)
  | draw
  | ongoing
  deriving DecidableEq

/-- S032 endpoint priority; optional current/intended claims are separate actions. -/
noncomputable def classify (s : RawTrace.State) : EndpointStatus := by
  classical
  exact if MatedK (RawTrace.erase s) then .mate (RawTrace.erase s).turn.opp
    else if DrawTrigger s then .draw else .ongoing

end EndgameChess.Rules.RawAdjudication
