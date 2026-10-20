import EndgameChess.Rules.HistoryLayer.Definitions
import EndgameChess.Rules.RawTrace.Soundness
import EndgameChess.Rules.StoppedHistory.AppendLifting
import EndgameChess.Rules.RawAdjudication.Ongoing
import EndgameChess.Rules.RawClaims.Definitions

/-! S064 / EC-C038: concrete RAW layer, not certified complete FIDE semantics. -/
namespace EndgameChess.Rules.RawHistoryLayer

/-- Retain the full actual initial-rooted trace and its strict-prefix proof. -/
def State := {s : RawTrace.State // StoppedHistory.Admissible s.trace}

def erase (s : State) : Position := RawTrace.erase s.val

def BoardStep (s t : State) : Prop := RawTrace.RawBoardStep s.val t.val

def Ongoing (s : State) : Prop := RawAdjudication.classify s.val = .ongoing

/-- Raw optional current/intended availability, not a FIDE claim-validity theorem. -/
def CanClaim (s : State) : Prop := RawClaims.AvailableThreshold s.val

/-- Every legal child is retained, including one whose endpoint is terminal. -/
def layer : HistoryLayer.Layer State where
  erase := erase
  BoardStep := BoardStep
  Ongoing := Ongoing
  CanClaim := CanClaim
  step_sound := by
    intro s t _ step
    exact RawTrace.raw_step_sound step
  reply_complete := by
    intro s r ongoing legal
    obtain ⟨t, admissible, step, endpoint⟩ :=
      (StoppedHistory.append_and_reply_lifting s.val).2 s.property ongoing r legal
    exact ⟨⟨t, admissible⟩, step, endpoint⟩
  ongoing_not_dead := by
    intro s ongoing
    exact ((RawAdjudication.ongoing_iff s.val).mp ongoing).1

end EndgameChess.Rules.RawHistoryLayer
