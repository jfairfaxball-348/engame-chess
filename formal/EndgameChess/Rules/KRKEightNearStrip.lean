import EndgameChess.Rules.KRKEightStrip
import EndgameChess.Rules.KRKSevenInner
import EndgameChess.Rules.KRKEightCentralStrip

namespace EndgameChess.Rules.KRKEightNearStrip
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000

def Prison (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ (sk.2.val = 1 ∨ sk.2.val = 2) ∧ rs.2.val = 3) ∨
  (sk.2.val = 4 ∧ sk.1.val ≤ 2 ∧ rs.1.val = 2) ∨
  (sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.1.val = 1) ∨
  (rs.1.val = 2 ∧ rs.2.val = 3)

theorem prison {sk rs : Square} (far : 2 ≤ dInf sk (1,2))
    (clear : KRKEightGeometry.Clear sk rs (1,2)) : Prison sk rs := by
  have cover : ∀ t, dInf ((1 : Fin 8),2) t = 1 → 0 < KRKEdgeDepth.depth t →
      ¬KRKSixInterior.InnerCorner t → Covered sk rs t := fun t distance inside notInner =>
    (KRKEightInterior.covered_or_inner clear.1 distance inside
      (fun u step => clear.2.2 u (KRKCornerWeakBand.step_guard step))).resolve_right notInner
  have a := covered_box (cover ((1 : Fin 8),3) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have b := covered_box (cover ((2 : Fin 8),1) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have c := covered_box (cover ((2 : Fin 8),2) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have d := covered_box (cover ((2 : Fin 8),3) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have safe := clear.1
  clear cover clear
  dsimp at a b c d
  simp only [show ((3 : Fin 8).val) = 3 from rfl] at a d
  have kingFar : 3 ≤ sk.1.val ∨ sk.2.val = 0 ∨ 4 ≤ sk.2.val := by
    dsimp [dInf,absDiff] at far
    omega
  have protection : 3 ≤ rs.1.val ∨ rs.2.val = 0 ∨ 4 ≤ rs.2.val ∨
      (sk.1.val ≤ rs.1.val + 1 ∧ rs.1.val ≤ sk.1.val + 1 ∧
       sk.2.val ≤ rs.2.val + 1 ∧ rs.2.val ≤ sk.2.val + 1) := by
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  clear far safe
  dsimp [Prison]
  by_cases file : rs.1.val = 1 <;> by_cases row : rs.2.val = 3 <;> omega

private theorem near_four_necessary {sk rs : Square} (sx : sk.1.val = 4) (ry : rs.2.val = 2)
    (seven : KRKSevenNear.Seven sk rs) : rs.1.val = 1 := by
  rcases seven with ⟨i,region,distance,_,_⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenNear.RookRegion,KRKSevenNear.LowRegion,KRKSevenNear.SideRegion,
      KRKSevenNear.king,dInf,absDiff] at region distance <;> omega
  · cases i <;> simp only [KRKSevenNear.king] at equal <;>
      have same := congrArg (fun s : Square => s.1.val) equal <;> dsimp at same <;> omega

theorem no_upper_king {sk rs : Square} (distinct : sk ≠ rs) (sy : sk.2.val = 4)
    (rx : rs.1.val = 2) (_far : 2 ≤ dInf sk (1,2)) : ¬KRKEightGeometry.Clear sk rs (1,2) := by
  intro clear
  have notOne : rs.2.val ≠ 1 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (0,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
    dsimp
    omega
  let g := Frame.ofSym symSwap
  have child := KRKSevenReach.frame_map g distinct
    (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have seven := (KRKSevenNear.clear_iff (g.ne_iff.mpr distinct) (g.ne_iff.mpr guard.2.1.symm)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mp child
  have result := near_four_necessary (sk := g.f sk) (rs := g.f rs) sy rx seven
  exact notOne result

theorem file_one_requires_row_three {sk rs : Square} (distinct : sk ≠ rs)
    (sx : sk.1.val = 3) (rx : rs.1.val = 1) (clear : KRKEightGeometry.Clear sk rs (1,2)) :
    rs.2.val = 3 := by
  by_cases notThree : rs.2.val = 3
  · exact notThree
  apply False.elim
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (0,3) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,rx]
    dsimp
    omega
  let g := Frame.ofSym symSwap
  have child := KRKSevenReach.frame_map g distinct
    (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have notKing : sk ≠ ((0 : Fin 8),3) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have formula := (KRKSevenMiddle.low_rook_clear_iff (sk := g.f sk) (rs := g.f rs) (wk := ((3 : Fin 8),0))
    rfl (by decide) (by decide) (by dsimp [g,Frame.ofSym,symSwap]; omega)
    (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing)
    (g.ne_iff.mpr guard.2.1.symm) (by
      change 2 ≤ dInf (g.f sk) (g.f ((0 : Fin 8),3))
      rw [g.distance]
      exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mp child
  have rank := formula.1
  dsimp [g,Frame.ofSym,symSwap] at rank
  omega

theorem row_three_necessary {sk rs : Square} (sx : sk.1.val = 3) (ry : rs.2.val = 3)
    (clear : KRKEightGeometry.Clear sk rs (1,2)) : sk.2.val = 1 ∧ 3 ≤ rs.1.val := by
  have safe := clear.1
  have notOne : rs.1.val ≠ 1 := by
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (1,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry]
    dsimp
    omega
  have condition := KRKSevenInner.inner_entry_necessary (clear.2.2 _ guard)
  dsimp [dInf,absDiff] at condition
  have sy : sk.2.val = 1 := by omega
  refine ⟨sy,?_⟩
  dsimp [SafeRook,dInf,absDiff] at safe
  omega

theorem necessary {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKEightGeometry.Clear sk rs (1,2)) : KRKEightStrip.Region sk rs (1,2) := by
  have choices := prison far clear
  rcases choices with ⟨sx,_,ry⟩ | ⟨sy,_,rx⟩ | ⟨sx,_,rx⟩ | ⟨rx,ry⟩
  · obtain ⟨sy,width⟩ := row_three_necessary sx ry clear
    exact ⟨rfl,rfl,sx,sy,ry,width⟩
  · exact False.elim (no_upper_king distinct sy rx far clear)
  · have ry := file_one_requires_row_three distinct sx rx clear
    obtain ⟨sy,width⟩ := row_three_necessary sx ry clear
    omega
  · have shape : sk.1.val = 3 ∨ sk.2.val = 4 := by
      have safe := clear.1
      dsimp [SafeRook,dInf,absDiff] at safe far
      omega
    rcases shape with sx | sy
    · have width := (row_three_necessary sx ry clear).2
      omega
    · exact False.elim (no_upper_king distinct sy rx far clear)

theorem clear_iff {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,2)) :
    KRKEightGeometry.Clear sk rs (1,2) ↔ KRKEightStrip.Region sk rs (1,2) :=
  ⟨necessary distinct far,KRKEightStrip.region_clear⟩

theorem kernel_eight_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2)) :
    MateWithin σ 8 q ↔ KRKEightStrip.Region sk rs (1,2) := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKEightGeometry.kernel_eight_iff material turn notMate).trans (clear_iff material.1 far)

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),2))
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKEightGeometry.Clear sk rs wk ↔ KRKEightStrip.Region (g.f sk) (g.f rs) (1,2) := by
  have mappedFar : 2 ≤ dInf (g.f sk) (1,2) := by rw [←target,g.distance]; exact far
  constructor
  · intro clear
    have mapped := KRKCastleEight.frame_map g distinct clear
    rw [target] at mapped
    exact necessary (g.ne_iff.mpr distinct) mappedFar mapped
  · intro region
    have mapped := KRKEightStrip.region_clear region
    rw [←target] at mapped
    have back := KRKCastleEight.frame_map g.inverse (g.ne_iff.mpr distinct) mapped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKEightNearStrip
