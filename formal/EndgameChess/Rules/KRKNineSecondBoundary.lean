import EndgameChess.Rules.KRKNineInnerBoundary

namespace EndgameChess.Rules.KRKNineSecondBoundary
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem frame_f (s : Square) : (KRKNineSlots.frame ((2 : Fin 8),0)).f s = s := rfl
private theorem frame_r (s : Square) : (KRKNineSlots.frame ((2 : Fin 8),0)).r s = s := rfl

private theorem region_clear {sk rs : Square} (distinct : sk ≠ rs)
    (region : KRKEightGlobal.Region sk rs (2,0)) : KRKEightGeometry.Clear sk rs (2,0) := by
  exact (KRKEightGlobal.edge_clear_iff distinct (by decide)).mpr region

private theorem middle_covered {sk rs : Square} (clear : KRKEightGeometry.Clear sk rs (2,0)) : Covered sk rs (2,1) := by
  exact (KRKEightInterior.covered_or_inner clear.1 (by decide) (by decide)
    (fun u step => clear.2.2 u (KRKCornerWeakBand.step_guard step))).resolve_right
    (by dsimp [KRKSixInterior.InnerCorner]; decide)

private theorem no_seven_near {rs : Square}
    (rook : (rs.1.val = 2 ∧ rs.2.val = 2) ∨ (rs.1.val = 3 ∧ rs.2.val = 1)) :
    ¬KRKSevenNear.Seven ((4 : Fin 8),2) rs := by
  rintro (⟨i,region,distance,_,_⟩ | ⟨i,equal,_⟩)
  · cases i <;> dsimp [KRKSevenNear.RookRegion,KRKSevenNear.LowRegion,KRKSevenNear.SideRegion,
      KRKSevenNear.king,dInf,absDiff] at region distance <;> omega
  · have file := congrArg (fun s : Square => s.1.val) equal
    cases i <;> dsimp [KRKSevenNear.king] at file <;> omega

/-- All strong alternatives fail at this protected-rook boundary. -/
theorem no_nine : ¬KRKNineGeometry.Clear ((4 : Fin 8),2) ((3 : Fin 8),2) ((2 : Fin 8),0) := by
  intro clear
  rcases clear with immediate | points | rays
  · simp only [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    dsimp at immediate
    omega
  · simp only [KRKNineGeometry.KingPoints,frame_f,frame_r] at points
    obtain ⟨i,distance,apart,far,region⟩ := points
    have cover := covered_box (middle_covered (region_clear apart region))
    dsimp [dInf,absDiff] at distance far
    simp only [ne_iff_coords] at apart
    dsimp at cover apart
    omega
  · simp only [KRKNineGeometry.RookRays,frame_f,frame_r] at rays
    obtain ⟨_,_,a,v,sees,notKing,_,region⟩ := rays
    let nr := a.target ((3 : Fin 8),2) v
    have eight : KRKEightGeometry.Clear (4,2) nr (2,0) := region_clear notKing.symm region
    have cover := covered_box (middle_covered eight)
    have line := sees.1
    have rook : (nr.1.val = 2 ∧ nr.2.val = 2) ∨ (nr.1.val = 3 ∧ nr.2.val = 1) := by
      dsimp [RookLine] at line
      dsimp [nr] at cover
      simp only [show ((3 : Fin 8).val) = 3 from rfl,show ((4 : Fin 8).val) = 4 from rfl] at cover line
      dsimp [nr]
      omega
    have guard : KRKCornerWeakBand.Guard ((4 : Fin 8),2) nr (2,0) (1,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      simp <;> omega
    exact no_seven_near rook ((KRKSevenNear.clear_iff notKing.symm guard.2.1.symm guard.2.2.2).mp
      (eight.2.2 _ guard))

end EndgameChess.Rules.KRKNineSecondBoundary
