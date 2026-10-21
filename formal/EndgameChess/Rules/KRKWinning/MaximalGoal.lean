import EndgameChess.Rules.KRKWinning.Definitions
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- Every maximal winning-safe compliant endpoint is actual named mate, never a claim. -/
theorem winning_maximal_goal {c : Colour} {π : Policy} {s t : State} {n : Nat}
    (legal : LegalPolicy c π) (safe : WinningSafety c π s)
    (path : PolicyPath c π n s t) (maximal : PolicyMaximal c π t) : G c t := by
  rcases (policy_maximal_iff_stopped legal t).mp maximal with terminal | ⟨ongoing,own,claim,_⟩
  · exact (safe n t path).1 terminal
  · exact False.elim (((safe n t path).2 ongoing).1 own claim)
end EndgameChess.Rules.KRKWinning
