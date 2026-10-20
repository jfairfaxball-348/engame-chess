import EndgameChess.Rules.KRKSetup.ClearAxisEntry
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000


theorem setup_horizontal_entry_budget {q : Position} {σ : Colour} {sk rs wk : Square}
    (hwall : KRKWallBudget σ B) (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hgap : 2 ≤ absDiff sk.1.val wk.1.val) (hy : rs.2.val ≠ sk.2.val)
    (hf : 2 ≤ absDiff rs.2.val wk.2.val) : MateWithin σ (B + 2) q := by
  by_cases hx : sk.1.val + 2 ≤ wk.1.val
  · exact setup_clear_axis_entry_budget hwall symSwap hq hx (Or.inl hy) hf
  · apply setup_clear_axis_entry_budget hwall symAnti hq
    · simp only [symAnti, absDiff] at *; omega
    · apply Or.inl
      simp only [symAnti]; omega
    · simp only [symAnti, absDiff] at *; omega

end EndgameChess.Rules
