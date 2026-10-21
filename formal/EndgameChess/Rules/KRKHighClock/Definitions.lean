import EndgameChess.Rules.KRKHolding.Equivalence
import EndgameChess.Rules.RawTrace.Origin
import EndgameChess.Rules.RawHistoryLayer.Projection
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer

/-- Retained KRK or board deadness, stronger than arbitrary terminal Region. -/
def Good (σ : Colour) (s : State) : Prop :=
  (∃ sk rs wk, IsKRK (erase s) σ sk rs wk) ∨ DeadK (erase s)
end EndgameChess.Rules.KRKHighClock
