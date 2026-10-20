import EndgameChess.Rules.KRKStrategy.KRK
import EndgameChess.Rules.RawHistoryLayer.Definitions
import EndgameChess.Rules.RawRepetition.CurrentAppend
import EndgameChess.Rules.RawClock.StepBound
namespace EndgameChess.Rules.RawHistoryLayer
open EndgameChess.KK

/-- Incoming full-history counts at all strictly lower WINNING raw ranks. -/
def LowerRankHistory (σ : Colour) (s : RawTrace.State) : Prop :=
  ∀ r : Position, ForceMate σ r → strategyRank σ r < strategyRank σ (RawTrace.erase s) →
    RawRepetition.occurrences s.trace r < 2
end EndgameChess.Rules.RawHistoryLayer
