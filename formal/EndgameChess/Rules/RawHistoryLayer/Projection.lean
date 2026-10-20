import EndgameChess.Rules.RawHistoryLayer.Definitions
import EndgameChess.Rules.HistoryLayer.Projection

/-! S064 / EC-C038: concrete raw certificates project with the SAME ply budget. -/
namespace EndgameChess.Rules.RawHistoryLayer

open EndgameChess.KK

/-- Conditional certificate projection; no certificate existence or converse. -/
theorem raw_ruleMateWithin_project (s : State) (σ : Colour) (n : Nat)
    (certificate : HistoryLayer.RuleMateWithin layer σ n s) :
    MateWithin σ n (erase s) := by
  exact HistoryLayer.ruleMateWithin_project layer certificate

end EndgameChess.Rules.RawHistoryLayer
