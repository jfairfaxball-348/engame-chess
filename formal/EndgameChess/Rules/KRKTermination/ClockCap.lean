import EndgameChess.Rules.KRKTermination.PathBound
namespace EndgameChess.Rules.KRKTermination
open EndgameChess.KK
open RawHistoryLayer

/-- All board paths from exact KRK: at most 150−h when ongoing, zero when terminal. -/
theorem krk_clock_cap {σ : Colour} {sk rs wk : Square} {s t : State} {n : Nat}
    (material : IsKRK (erase s) σ sk rs wk) (path : Path n s t) :
    (Ongoing s → n ≤ 150 - RawClock.clock s.val.trace) ∧
      (¬Ongoing s → n = 0) := by
  classical
  have bound := (path_bound (Or.inl ⟨sk,rs,wk,material⟩) path).2
  constructor
  · intro ongoing
    simp only [fuel, if_pos ongoing] at bound
    omega
  · intro terminal
    simp only [fuel, if_neg terminal] at bound
    omega
end EndgameChess.Rules.KRKTermination
