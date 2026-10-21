import EndgameChess.Rules.KRKTermination.TerminalExists
import EndgameChess.Rules.KRKTermination.ClockCap
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer

abbrev W (c : Colour) (n : Nat) (s : State) : Prop :=
  HistoryLayer.RuleMateWithin layer c n s
abbrev F (c : Colour) (s : State) : Prop := HistoryLayer.RuleForceMate layer c s
abbrev G (c : Colour) (s : State) : Prop := HistoryLayer.Goal layer c s

/-- None is a correct zero-board-ply claim; Some is an actual admitted child. -/
abbrev Policy := State → Option State

def LegalPolicy (c : Colour) (π : Policy) : Prop :=
  ∀ s, Ongoing s → (erase s).turn = c →
    match π s with
    | none => CanClaim s
    | some t => BoardStep s t

/-- All opponent board replies; own moves must equal the policy choice. -/
inductive PolicyPath (c : Colour) (π : Policy) : Nat → State → State → Prop
  | refl (s : State) : PolicyPath c π 0 s s
  | cons {n : Nat} {s u t : State} : BoardStep s u →
      ((erase s).turn = c → π s = some u) →
      PolicyPath c π n u t → PolicyPath c π (n+1) s t

def Safe (c : Colour) (π : Policy) (s : State) : Prop :=
  ∀ n t, PolicyPath c π n s t → ¬G c.opp t

/-- Actual legal strategy and all-compliant-prefix safety, independent of forcing. -/
def RuleHold (c : Colour) (s : State) : Prop :=
  ∃ π, LegalPolicy c π ∧ Safe c π s

def Stopped (c : Colour) (π : Policy) (s : State) : Prop :=
  ¬Ongoing s ∨ (Ongoing s ∧ (erase s).turn = c ∧ π s = none ∧ CanClaim s)

def PolicyMaximal (c : Colour) (π : Policy) (s : State) : Prop :=
  ¬∃ t, BoardStep s t ∧ ((erase s).turn = c → π s = some t)
end EndgameChess.Rules.KRKHolding
