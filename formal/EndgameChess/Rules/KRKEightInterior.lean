import EndgameChess.Rules.KRKSevenMiddle

namespace EndgameChess.Rules.KRKEightInterior
open EndgameChess.KK KRKFourPlyEscape
set_option maxHeartbeats 400000

theorem covered_or_inner {sk rs wk t : Square} (safe : SafeRook sk rs wk)
    (distance : dInf wk t = 1) (inside : 0 < KRKEdgeDepth.depth t)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKSevenGeometry.Clear sk rs u) :
    Covered sk rs t ∨ KRKSixInterior.InnerCorner t := by
  by_cases inner : KRKSixInterior.InnerCorner t
  · exact Or.inr inner
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl (Or.inl king)
  by_cases line : RookLine rs t
  · exact Or.inl (Or.inr line)
  have apart : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ :=
    StepM.lone distance apart (by omega) (fun seen => line seen.1)
  have domain := KRKSevenReach.weak_domain (every t step)
  exact False.elim (domain.elim (by omega) inner)

theorem deep_escape {sk rs wk : Square} (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk)
    (xl : 2 ≤ wk.1.val) (xh : wk.1.val ≤ 5) (yl : 2 ≤ wk.2.val) (yh : wk.2.val ≤ 5)
    (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKSevenGeometry.Clear sk rs u) : False := by
  let left : Fin 8 := ⟨wk.1.val-1,by omega⟩
  let right : Fin 8 := ⟨wk.1.val+1,by omega⟩
  let down : Fin 8 := ⟨wk.2.val-1,by omega⟩
  let up : Fin 8 := ⟨wk.2.val+1,by omega⟩
  have cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → ¬KRKSixInterior.InnerCorner t → Covered sk rs t :=
    fun t distance inside notInner => (covered_or_inner safe distance inside every).resolve_right notInner
  have a := covered_box (cover (left,wk.2)
    (by simp [left,dInf,absDiff] <;> omega) (by dsimp [left,KRKEdgeDepth.depth]; omega)
    (by dsimp [left,KRKSixInterior.InnerCorner]; omega))
  have b := covered_box (cover (right,wk.2)
    (by simp [right,dInf,absDiff] <;> omega) (by dsimp [right,KRKEdgeDepth.depth]; omega)
    (by dsimp [right,KRKSixInterior.InnerCorner]; omega))
  have c := covered_box (cover (wk.1,down)
    (by simp [down,dInf,absDiff] <;> omega) (by dsimp [down,KRKEdgeDepth.depth]; omega)
    (by dsimp [down,KRKSixInterior.InnerCorner]; omega))
  have d := covered_box (cover (wk.1,up)
    (by simp [up,dInf,absDiff] <;> omega) (by dsimp [up,KRKEdgeDepth.depth]; omega)
    (by dsimp [up,KRKSixInterior.InnerCorner]; omega))
  clear every cover safe
  dsimp [left,right,down,up] at a b c d
  simp only [dInf,absDiff] at far
  simp only [ne_iff_coords] at notRook
  omega

theorem weak_eight_depth_le_one {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (win : MateWithin σ 8 q) : KRKEdgeDepth.depth wk ≤ 1 := by
  by_cases shallow : KRKEdgeDepth.depth wk ≤ 1
  · exact shallow
  have deep : 2 ≤ wk.1.val ∧ wk.1.val ≤ 5 ∧ 2 ≤ wk.2.val ∧ wk.2.val ≤ 5 := by
    dsimp [KRKEdgeDepth.depth] at shallow
    omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  have clear := (KRKEightGeometry.kernel_eight_iff material turn notMate).mp win
  exact False.elim (deep_escape material.2.2.1 far deep.1 deep.2.1 deep.2.2.1 deep.2.2.2 clear.1
    (fun t step => clear.2.2 t (KRKCornerWeakBand.step_guard step)))

end EndgameChess.Rules.KRKEightInterior
