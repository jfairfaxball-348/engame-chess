import EndgameChess.Rules.KRKHighClock.StrongHold
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- The lone side has no RAW mate-forcing certificate at any admitted KRK root. -/
theorem weak_not_force {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) : ¬F σ.opp s :=
  not_force_of_hold (strong_hold material)
end EndgameChess.Rules.KRKHighClock
