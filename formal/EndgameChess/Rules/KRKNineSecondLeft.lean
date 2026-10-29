import EndgameChess.Rules.KRKNineInner

namespace EndgameChess.Rules.KRKNineSecondLeft
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem frame_f (s : Square) : (KRKNineSlots.frame ((2 : Fin 8),0)).f s = s := rfl
private theorem frame_r (s : Square) : (KRKNineSlots.frame ((2 : Fin 8),0)).r s = s := rfl

private theorem region_clear {sk rs : Square} (distinct : sk ≠ rs)
    (region : KRKEightGlobal.Region sk rs (2,0)) : KRKEightGeometry.Clear sk rs (2,0) :=
  (KRKEightGlobal.edge_clear_iff distinct (by decide)).mpr region

private theorem eight_no_left_high {rs : Square} (distinct : ((1 : Fin 8),3) ≠ rs) :
    ¬KRKEightGeometry.Clear ((1 : Fin 8),3) rs (2,0) := by
  intro clear
  have cover : ∀ t, dInf ((2 : Fin 8),0) t = 1 → 0 < KRKEdgeDepth.depth t →
      ¬KRKSixInterior.InnerCorner t → Covered (1,3) rs t := fun t distance inside notInner =>
    (KRKEightInterior.covered_or_inner clear.1 distance inside
      (fun u step => clear.2.2 u (KRKCornerWeakBand.step_guard step))).resolve_right notInner
  have a := covered_box (cover ((2 : Fin 8),1) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have b := covered_box (cover ((3 : Fin 8),1) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have row : rs.2.val = 1 := by dsimp at a b; omega
  have notThree : rs.1.val ≠ 3 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard ((1 : Fin 8),3) rs (2,0) (3,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  have middle := (KRKSevenMiddle.low_rook_clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) (by decide)
    (by omega) distinct (by decide) guard.2.1.symm guard.2.2.1 guard.2.2.2).mp (clear.2.2 _ guard)
  have rank := middle.1
  change 3 = 2 at rank
  contradiction

/-- The near inward-corner root has no nine-ply entry when this rook is
too far right on rank one. All first king and rook moves are covered. -/
theorem no_nine {rs : Square} (width : 5 ≤ rs.1.val) (row : rs.2.val = 1) :
    ¬KRKNineGeometry.Clear ((1 : Fin 8),3) rs (2,0) := by
  intro clear
  rcases clear with immediate | points | rays
  · simp only [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    dsimp at immediate
    omega
  · simp only [KRKNineGeometry.KingPoints,frame_f,frame_r] at points
    obtain ⟨i,distance,apart,_,region⟩ := points
    have eight := region_clear apart region
    have x : (KRKNineSlots.point i).1.val ≤ 2 := by dsimp [dInf,absDiff] at distance; omega
    have y : 2 ≤ (KRKNineSlots.point i).2.val := by dsimp [dInf,absDiff] at distance; omega
    have guard : KRKCornerWeakBand.Guard (KRKNineSlots.point i) rs (2,0) (3,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
      simp <;> omega
    have middle := (KRKSevenMiddle.low_rook_clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) (by decide)
      (by omega) apart (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2).mp
      (eight.2.2 _ guard)
    dsimp [KRKFiveMiddle.LowRookFive] at middle
    omega
  · simp only [KRKNineGeometry.RookRays,frame_f,frame_r] at rays
    obtain ⟨_,_,_,_,_,notKing,_,region⟩ := rays
    exact eight_no_left_high notKing.symm (region_clear notKing.symm region)

end EndgameChess.Rules.KRKNineSecondLeft
