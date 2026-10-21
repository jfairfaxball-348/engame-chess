import EndgameChess.Rules.KRKHighClock.Terminal
import EndgameChess.Rules.KRKHolding.StoppedExists
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- Every prefix has correct terminal outcome and preserves all claim actions. -/
def WinningSafety (c : Colour) (π : Policy) (s : State) : Prop :=
  ∀ n t, PolicyPath c π n s t →
    (¬Ongoing t → G c t) ∧
    (Ongoing t → ((erase t).turn = c → π t ≠ none) ∧
      ((erase t).turn = c.opp → ¬CanClaim t))

/-- Independent actual strategy semantics, including a uniform finite horizon. -/
def ActualWin (c : Colour) (s : State) : Prop :=
  ∃ π : Policy, ∃ B : Nat, LegalPolicy c π ∧ WinningSafety c π s ∧
    ∀ n t, PolicyPath c π n s t → n ≤ B
end EndgameChess.Rules.KRKWinning
