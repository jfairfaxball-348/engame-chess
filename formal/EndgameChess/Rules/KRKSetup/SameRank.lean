import EndgameChess.Rules.KRKSetup.WeakWall
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000

/-- Same-rank strong king and rook can make a wall by a backwards king step. -/
theorem setup_same_rank_budget {q : Position} {σ : Colour} {sk rs wk : Square}
    (hwall : KRKWallBudget σ B)
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hg : sk.2.val + 2 ≤ wk.2.val) (hy : rs.2.val = sk.2.val)
    (hpos : 0 < sk.2.val) (hn : ¬ RookSees rs wk sk wk) : MateWithin σ (B + 2) q := by
  have hx := bound_same_rank_no_file (sk := sk) (rs := rs) (wk := wk) hq.1.1 hy hg hn
  let su : Square := (sk.1, ⟨sk.2.val - 1, by omega⟩)
  have hsy : su.2.val + 1 = sk.2.val := by dsimp [su]; omega
  have hs : StepM ⟨sk, rs, wk, true⟩ ⟨su, rs, wk, false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;> dsimp only [su] <;>
      simp only [dInf, absDiff, ne_iff_coords] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hs
  let t : Square := (wk.1, ⟨wk.2.val - 1, by omega⟩)
  have hrep : StepM ⟨su, rs, wk, false⟩ ⟨su, rs, t, true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      (try dsimp only [su, t] at *) <;>
      simp only [dInf, absDiff, ne_iff_coords, RookSees, RookLine, OnSeg] at * <;> omega
  obtain ⟨r, hr, _⟩ := step_sound hm hrep
  apply mateWithin_choose hq.2 hl
  apply setup_weak_wall_budget hwall hm (by omega) (by omega) ?_ ⟨r, hr⟩
  exact Or.inl (by simp only [dInf, absDiff] at *; omega)
end EndgameChess.Rules
