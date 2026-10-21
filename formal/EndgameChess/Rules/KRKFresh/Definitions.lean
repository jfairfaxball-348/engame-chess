import EndgameChess.Rules.KRKWinning.Equivalence
import EndgameChess.Rules.KRKSharper.RawWall
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK RawHistoryLayer

def Query (σ : Colour) (q : Position) : Prop := ∃ sk rs wk, IsKRK q σ sk rs wk

def Ever {q : Position} (σ : Colour) (t : RawTrace.Trace q) : Prop :=
  ∃ p, p ∈ t.positions ∧ Query σ p

/-- Only future exact KRK queries, never the older all-material histogram. -/
def History (σ : Colour) (s : RawTrace.State) : Prop :=
  ∀ r, Query σ r → ForceMate σ r →
    strategyRank σ r < strategyRank σ (RawTrace.erase s) → RawRepetition.occurrences s.trace r < 2
end EndgameChess.Rules.KRKFresh
