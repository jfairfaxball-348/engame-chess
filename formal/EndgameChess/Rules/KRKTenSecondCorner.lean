import EndgameChess.Rules.KRKTenGeometry
import EndgameChess.Rules.KRKNineNearStrip
import EndgameChess.Rules.KRKEightCentralStripHolding

namespace EndgameChess.Rules.KRKTenSecondCorner
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem nine_middle_not_clear {sk rs t : Square} (distinct : sk ≠ rs) (notKing : sk ≠ t)
    (notRook : rs ≠ t) (far : 2 ≤ dInf sk t) (notCheck : ¬RookSees rs t sk t)
    (middle : KRKEightCentralStrip.MiddleStrip t) : ¬KRKNineGeometry.Clear sk rs t := by
  intro clear
  let q := krkPos .white sk rs t .white
  have material : IsKRK q .white sk rs t := ⟨distinct,notKing,notRook,rfl⟩
  have nine := KRKNineGeometry.sufficient material rfl far notCheck clear
  exact KRKEightCentralStripHolding.strong_no_ten material rfl middle (mateWithin_mono nine (by decide))

theorem bad_neighbour_covered {sk rs wk t : Square} (distinct : sk ≠ rs)
    (clear : KRKTenGeometry.Clear sk rs wk) (distance : dInf wk t = 1)
    (bad : 2 ≤ KRKEdgeDepth.depth t ∨ KRKEightCentralStrip.MiddleStrip t) : Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have notRook : t ≠ rs := by
    intro equal
    have safe := clear.1
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have far : 2 ≤ dInf sk t := by omega
  have notCheck : ¬RookSees rs t sk t := fun seen => line seen.1
  have guard : KRKCornerWeakBand.Guard sk rs wk t := ⟨distance,notRook,far,notCheck⟩
  have nine := clear.2.2 t guard
  rcases bad with deep | middle
  · have shallow := KRKTenGeometry.nine_weak_depth nine
    omega
  · exact False.elim (nine_middle_not_clear distinct (ne_of_dInf_pos (by omega)) notRook.symm far notCheck middle nine)

/-- Covering the five destinations outside the nine-ply weak-square domain
forces a fourth-file king/third-rank rook, or the transposed configuration. -/
theorem prison {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (2,2))
    (clear : KRKTenGeometry.Clear sk rs (2,2)) :
    (sk.1.val = 4 ∧ rs.2.val = 3) ∨ (sk.2.val = 4 ∧ rs.1.val = 3) := by
  have a := covered_box (bad_neighbour_covered distinct clear (t := (1,3)) (by decide) (Or.inr (by
    exact Or.inl ⟨Or.inl rfl,by decide,by decide⟩)))
  have b := covered_box (bad_neighbour_covered distinct clear (t := (2,3)) (by decide) (Or.inl (by decide)))
  have c := covered_box (bad_neighbour_covered distinct clear (t := (3,1)) (by decide) (Or.inr (by
    exact Or.inr ⟨Or.inl rfl,by decide,by decide⟩)))
  have d := covered_box (bad_neighbour_covered distinct clear (t := (3,2)) (by decide) (Or.inl (by decide)))
  have e := covered_box (bad_neighbour_covered distinct clear (t := (3,3)) (by decide) (Or.inl (by decide)))
  have safe := clear.1
  clear clear
  dsimp [SafeRook,dInf,absDiff] at safe far
  dsimp at a b c d e
  omega

private theorem near_necessary {sk rs : Square} (distinct : sk ≠ rs) (notKing : sk ≠ ((1 : Fin 8),2))
    (notRook : rs ≠ ((1 : Fin 8),2)) (far : 2 ≤ dInf sk (1,2))
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) (clear : KRKNineGeometry.Clear sk rs (1,2)) :
    KRKNineNearStrip.Nine sk rs := by
  let q := krkPos .white sk rs (1,2) .white
  have material : IsKRK q .white sk rs (1,2) := ⟨distinct,notKing,notRook,rfl⟩
  exact KRKNineNearStrip.necessary material rfl (KRKNineGeometry.sufficient material rfl far notCheck clear)

theorem horizontal_escape {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 4)
    (ry : rs.2.val = 3) : ¬KRKTenGeometry.Clear sk rs (2,2) := by
  intro clear
  have notTwo : rs.1.val ≠ 2 := by
    intro same
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (2,2) (2,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKNineGeometry.frame_map g distinct notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have condition := near_necessary (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing)
    (g.ne_iff.mpr guard.2.1.symm) (by
      change 2 ≤ dInf (g.f sk) (g.f ((2 : Fin 8),1))
      rw [g.distance]; exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
  dsimp [KRKNineNearStrip.Nine,g,Frame.ofSym,symSwap,dInf,absDiff] at condition
  simp only [square_eq_iff,Fin.ext_iff] at condition
  dsimp at condition
  omega

theorem not_clear {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (2,2)) :
    ¬KRKTenGeometry.Clear sk rs (2,2) := by
  intro clear
  rcases prison distinct far clear with ⟨sx,ry⟩ | ⟨sy,rx⟩
  · exact horizontal_escape distinct sx ry clear
  · have mapped := KRKTenGeometry.frame_map (Frame.ofSym symSwap) distinct clear
    exact horizontal_escape (symSwap.ne_iff.mpr distinct) sy rx mapped

theorem framed_not_clear (g : Frame) {sk rs wk : Square} (target : g.f wk = ((2 : Fin 8),2))
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) : ¬KRKTenGeometry.Clear sk rs wk := by
  intro clear
  have mapped := KRKTenGeometry.frame_map g distinct clear
  have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
  rw [target] at mapped mappedFar
  exact not_clear (g.ne_iff.mpr distinct) mappedFar mapped

theorem kernel_no_ten {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (2,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (2,2)) :
    ¬MateWithin σ 10 q := by
  intro ten
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 2 = 0 at zero
    contradiction
  exact not_clear material.1 far ((KRKTenGeometry.kernel_ten_iff material turn notMate).mp ten)

theorem framed_kernel_no_ten (g : Frame) {q : Position} {σ : Colour} {sk rs wk : Square}
    (target : g.f wk = ((2 : Fin 8),2)) (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < KRKEdgeDepth.depth wk) : ¬MateWithin σ 10 q := by
  intro ten
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  exact framed_not_clear g target material.1 far ((KRKTenGeometry.kernel_ten_iff material turn notMate).mp ten)

end EndgameChess.Rules.KRKTenSecondCorner
