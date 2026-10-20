import EndgameChess.Rules.KRKSharper.Pursuit
namespace EndgameChess.Rules
open EndgameChess.KK
/-- Either direct orientation is constructed; no move-graph reflection is used. -/
theorem krk_lower_band_bound_of_exits_sharper {σ : Colour} {y E : Nat}
    (hexit : LowerExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hsy : sk.2.val + 1 = y) (hry : rs.2.val = y) (hwy : wk.2.val = y + 1)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) : MateWithin σ (50 + E) q := by
  by_cases he : sk.1.val = wk.1.val
  · exact mateWithin_mono (hexit hq hsy hry hf (Or.inr ⟨hwy, he⟩)) (by omega)
  by_cases hx : sk.1.val < wk.1.val
  · exact mateWithin_mono (krk_oriented_lower_bound_sharper true hexit hq hsy hry hwy hf hx) (by have := pursuitFile_bound true sk; omega)
  · apply mateWithin_mono (krk_oriented_lower_bound_sharper false hexit hq hsy hry hwy hf ?_) (by have := pursuitFile_bound false sk; omega)
    simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte]
    omega

end EndgameChess.Rules
