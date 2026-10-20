import EndgameChess.Rules.RawClock.ExtensionBound

/-! S040 / EC-C026: conditional clock certificate, not claim adjudication. -/
namespace EndgameChess.Rules.RawClock

/-- A strict root budget covers every prefix and every interior prospective ply. -/
theorem clock_budget_certificate {s : RawTrace.State} {n : Nat}
    (budget : clock s.trace + n < 100) {k : Nat} {u : RawTrace.State}
    (depth : k ≤ n) (path : RawTrace.Extends k s u) :
    clock u.trace < 100 ∧
      (k < n → ∀ {v : RawTrace.State}, RawTrace.RawBoardStep u v → clock v.trace < 100) := by
  constructor
  · exact Nat.lt_of_le_of_lt
      (Nat.le_trans (clock_le_extension path) (Nat.add_le_add_left depth _)) budget
  · intro interior v step
    have extended := RawTrace.Extends.snoc path step
    have nextDepth : k + 1 ≤ n := Nat.succ_le_of_lt interior
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans (clock_le_extension extended) (Nat.add_le_add_left nextDepth _)) budget

end EndgameChess.Rules.RawClock
