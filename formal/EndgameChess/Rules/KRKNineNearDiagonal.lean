import EndgameChess.Rules.KRKNineSecondLeft

namespace EndgameChess.Rules.KRKNineNearDiagonal
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem frame_f (s : Square) : (KRKNineSlots.frame ((1 : Fin 8),0)).f s = s := rfl
private theorem frame_r (s : Square) : (KRKNineSlots.frame ((1 : Fin 8),0)).r s = s := rfl

private theorem region_clear {sk rs : Square} (distinct : sk ≠ rs)
    (region : KRKEightGlobal.Region sk rs (1,0)) : KRKEightGeometry.Clear sk rs (1,0) :=
  (KRKEightGlobal.edge_clear_iff distinct (by decide)).mpr region

theorem no_nine : ¬KRKNineGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) ((1 : Fin 8),0) := by
  intro clear
  rcases clear with immediate | points | rays
  · simp only [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    dsimp at immediate
    omega
  · simp only [KRKNineGeometry.KingPoints,frame_f,frame_r] at points
    obtain ⟨i,distance,apart,_,region⟩ := points
    have eight := region_clear apart region
    have guard : KRKCornerWeakBand.Guard (KRKNineSlots.point i) ((2 : Fin 8),2) (1,0) (1,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      simp <;> simp only [ne_iff_coords] at apart <;> dsimp [dInf,absDiff] at distance apart <;> omega
    have necessary := KRKSevenInner.inner_entry_necessary (eight.2.2 _ guard)
    dsimp [dInf,absDiff] at distance necessary
    simp only [ne_iff_coords] at apart
    dsimp at apart
    omega
  · simp only [KRKNineGeometry.RookRays,frame_f,frame_r] at rays
    obtain ⟨_,_,a,v,sees,notKing,_,region⟩ := rays
    let nr := a.target ((2 : Fin 8),2) v
    have eight : KRKEightGeometry.Clear (3,3) nr (1,0) := region_clear notKing.symm region
    have cover := covered_box ((KRKEightInterior.covered_or_inner eight.1 (t := ((2 : Fin 8),1))
      (by decide) (by decide) (fun u step => eight.2.2 u (KRKCornerWeakBand.step_guard step))).resolve_right
      (by dsimp [KRKSixInterior.InnerCorner]; decide))
    have safe := eight.1
    have line := sees.1
    have notRow : nr.2.val ≠ 1 := by
      dsimp [RookLine] at line
      dsimp [nr,SafeRook,dInf,absDiff] at safe ⊢
      omega
    have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),3) nr (1,0) (1,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp at cover
      simp <;> omega
    have necessary := KRKSevenInner.inner_entry_necessary (eight.2.2 _ guard)
    dsimp [dInf,absDiff] at necessary
    omega

end EndgameChess.Rules.KRKNineNearDiagonal
