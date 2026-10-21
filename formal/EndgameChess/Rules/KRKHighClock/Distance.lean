import EndgameChess.Rules.KRKHighClock.StrongHighClock
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- Exact one-board-ply optimal budget on the winning high-clock strong family. -/
theorem high_clock_exact_one {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 98 ≤ RawClock.clock s.val.trace) :
    (F σ s ↔ W σ 1 s) ∧ ¬W σ 0 s := by
  constructor
  · constructor
    · intro win
      obtain ⟨t,edge,goal⟩ := (strong_high_clock_iff material ongoing turn high).mp win
      exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,goal⟩⟩
    · intro win
      exact ⟨1,win⟩
  · intro goal
    exact goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
end EndgameChess.Rules.KRKHighClock
