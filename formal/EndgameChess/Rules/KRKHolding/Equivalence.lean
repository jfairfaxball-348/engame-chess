import EndgameChess.Rules.KRKHolding.Safety
import EndgameChess.Rules.KRKHolding.Converse
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Genuine strategy/complement duality on EVERY admitted KRK-or-terminal history. -/
theorem holding_iff_not_force {σ c : Colour} {s : State} (region : Region σ s) :
    RuleHold c s ↔ ¬F c.opp s :=
  ⟨not_force_of_hold,hold_of_not_force region⟩
end EndgameChess.Rules.KRKHolding
