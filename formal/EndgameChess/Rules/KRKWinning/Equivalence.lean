import EndgameChess.Rules.KRKWinning.FromForce
import EndgameChess.Rules.KRKWinning.Certificate
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding KRKTermination

/-- Actual winning-policy semantics equals full forcing on every admitted KRK Region. -/
theorem actual_win_iff_force {σ c : Colour} {s : State} (region : Region σ s) :
    ActualWin c s ↔ F c s := by
  constructor
  · rintro ⟨π,B,legal,safe,bound⟩
    exact ⟨B,policy_certificate legal B s safe bound⟩
  · exact actual_win_of_force region
end EndgameChess.Rules.KRKWinning
