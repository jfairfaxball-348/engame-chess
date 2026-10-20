import EndgameChess.Rules.KRKBound.ClearAxisEntry
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

theorem krk_horizontal_entry_bound {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hgap : 2 ≤ absDiff sk.1.val wk.1.val)
    (hy : rs.2.val ≠ sk.2.val)
    (hf : 2 ≤ absDiff rs.2.val wk.2.val) : MateWithin σ 506 q := by
  by_cases hx : sk.1.val + 2 ≤ wk.1.val
  · exact krk_axis_entry_bound symSwap hq hx hy hf
  · apply krk_axis_entry_bound symAnti hq
    · simp only [symAnti, absDiff] at *; omega
    · simp only [symAnti]; omega
    · simp only [symAnti, absDiff] at *; omega
end EndgameChess.Rules
