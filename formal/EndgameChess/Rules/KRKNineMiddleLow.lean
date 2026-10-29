import EndgameChess.Rules.KRKTenInterior

namespace EndgameChess.Rules.KRKNineMiddleLow
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

theorem eight_no_high_king {sk rs : Square} (distinct : sk ≠ rs) (high : 3 ≤ sk.2.val) :
    ¬KRKEightGeometry.Clear sk rs (3,0) := by
  intro clear
  have cover : ∀ t, dInf ((3 : Fin 8),0) t = 1 → 0 < KRKEdgeDepth.depth t →
      ¬KRKSixInterior.InnerCorner t → Covered sk rs t := fun t distance inside notInner =>
    (KRKEightInterior.covered_or_inner clear.1 distance inside
      (fun u step => clear.2.2 u (KRKCornerWeakBand.step_guard step))).resolve_right notInner
  have a := covered_box (cover ((2 : Fin 8),1) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have b := covered_box (cover ((3 : Fin 8),1) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have c := covered_box (cover ((4 : Fin 8),1) (by decide) (by decide) (by dsimp [KRKSixInterior.InnerCorner]; decide))
  have row : rs.2.val = 1 := by dsimp at a b c; omega
  have notFour : rs.1.val ≠ 4 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (3,0) (4,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  have formula := (KRKSevenMiddle.low_rook_clear_iff (wk := ((4 : Fin 8),0))
    rfl (by decide) (by decide) (by omega) distinct
    (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2).mp
    (clear.2.2 _ guard)
  exact Nat.not_succ_le_self 2 (Nat.le_trans high (Nat.le_of_eq formula.1))

private theorem region_clear {sk rs : Square} (distinct : sk ≠ rs)
    (region : KRKEightGlobal.Region sk rs (3,0)) : KRKEightGeometry.Clear sk rs (3,0) := by
  have canonical : KRKEightEdge.Region sk rs (3,0) := by
    simpa [KRKEightGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      show ((3 : Fin 8).val) = 3 from rfl] using region
  exact (KRKEightEdge.clear_iff rfl (by decide) distinct).mpr canonical

private theorem second_no_seven {sk rs : Square} (sx : sk.1.val = 4) (sy : sk.2.val = 2)
    (rx : rs.1.val ≤ 2) (ry : rs.2.val = 1) : ¬KRKSevenSecond.Seven sk rs := by
  rintro (⟨i,region,distance⟩ | ⟨i,equal,_⟩)
  · cases i <;> dsimp [KRKSevenSecond.RookRegion,KRKSevenSecond.king,dInf,absDiff] at region distance <;> omega
  · have file := congrArg (fun s : Square => s.1.val) equal
    cases i <;> dsimp [KRKSevenSecond.king] at file <;> omega

theorem eight_low_necessary {sk rs : Square} (distinct : sk ≠ rs) (sy : sk.2.val = 2)
    (rx : rs.1.val ≤ 2) (ry : rs.2.val = 1) : ¬KRKEightGeometry.Clear sk rs (3,0) := by
  intro clear
  have east : KRKCornerWeakBand.Guard sk rs (3,0) (4,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,ry]
    simp <;> omega
  have middle := (KRKSevenMiddle.low_rook_clear_iff (wk := ((4 : Fin 8),0))
    rfl (by decide) (by decide) (by omega) distinct
    (ne_of_dInf_pos (by have h := east.2.2.1; omega)) east.2.1.symm east.2.2.1 east.2.2.2).mp
    (clear.2.2 _ east)
  have sx : sk.1.val = 4 := by dsimp [KRKFiveMiddle.LowRookFive] at middle; omega
  have notTwo : rs.1.val ≠ 2 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have west : KRKCornerWeakBand.Guard sk rs (3,0) (2,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry]
    simp <;> omega
  exact second_no_seven sx sy rx ry ((KRKSevenSecond.clear_iff distinct west.2.1.symm west.2.2.2).mp
    (clear.2.2 _ west))

/-- With a rank-three king, a low rook on files 0..2 cannot force nine
plies at the central edge square (3,0), against any strong move choice. -/
theorem no_nine {sk rs : Square} (_distinct : sk ≠ rs) (sy : sk.2.val = 3)
    (rx : rs.1.val ≤ 2) (ry : rs.2.val = 1) : ¬KRKNineGeometry.Clear sk rs (3,0) := by
  intro clear
  have frameF (s : Square) : (KRKNineSlots.frame ((3 : Fin 8),0)).f s = s := by
    simp [KRKNineSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      show ((3 : Fin 8).val) = 3 from rfl]
  have frameR (s : Square) : (KRKNineSlots.frame ((3 : Fin 8),0)).r s = s := by
    simp [KRKNineSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      show ((3 : Fin 8).val) = 3 from rfl]
  rcases clear with immediate | points | rays
  · simp only [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget,sy] at immediate
    dsimp at immediate
    omega
  · simp only [KRKNineGeometry.KingPoints,frameF,frameR] at points
    obtain ⟨i,distance,apart,_,region⟩ := points
    have eight := region_clear apart region
    have low : (KRKNineSlots.point i).2.val ≤ 2 := by
      by_cases high : 3 ≤ (KRKNineSlots.point i).2.val
      · exact False.elim (eight_no_high_king apart high eight)
      · omega
    have row : (KRKNineSlots.point i).2.val = 2 := by dsimp [dInf,absDiff] at distance; omega
    exact eight_low_necessary apart row rx ry eight
  · simp only [KRKNineGeometry.RookRays,frameF,frameR] at rays
    obtain ⟨_,_,a,v,_,notKing,_,region⟩ := rays
    exact eight_no_high_king notKing.symm (by omega) (region_clear notKing.symm region)

theorem king_two_three_necessary {sk rs : Square} (sx : sk.1.val = 2) (sy : sk.2.val = 3)
    (ry : rs.2.val = 1) (clear : KRKNineGeometry.Clear sk rs (3,0)) : rs.1.val = 4 ∨ rs.1.val = 5 := by
  have frameF (s : Square) : (KRKNineSlots.frame ((3 : Fin 8),0)).f s = s := by
    simp [KRKNineSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      show ((3 : Fin 8).val) = 3 from rfl]
  have frameR (s : Square) : (KRKNineSlots.frame ((3 : Fin 8),0)).r s = s := by
    simp [KRKNineSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      show ((3 : Fin 8).val) = 3 from rfl]
  rcases clear with immediate | points | rays
  · simp only [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget,sy] at immediate
    dsimp at immediate
    omega
  · simp only [KRKNineGeometry.KingPoints,frameF,frameR] at points
    obtain ⟨i,distance,apart,_,region⟩ := points
    have eight := region_clear apart region
    have low : (KRKNineSlots.point i).2.val ≤ 2 := by
      by_cases high : 3 ≤ (KRKNineSlots.point i).2.val
      · exact False.elim (eight_no_high_king apart high eight)
      · omega
    have row : (KRKNineSlots.point i).2.val = 2 := by dsimp [dInf,absDiff] at distance; omega
    have file : (KRKNineSlots.point i).1.val ≤ 3 := by dsimp [dInf,absDiff] at distance; omega
    by_cases four : rs.1.val = 4
    · exact Or.inl four
    have guard : KRKCornerWeakBand.Guard (KRKNineSlots.point i) rs (3,0) (4,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row,ry]
      simp <;> omega
    have formula := (KRKSevenMiddle.low_rook_clear_iff (wk := ((4 : Fin 8),0))
      rfl (by decide) (by decide) (by omega) apart
      (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2).mp
      (eight.2.2 _ guard)
    dsimp [KRKFiveMiddle.LowRookFive] at formula
    exact Or.inr (by omega)
  · simp only [KRKNineGeometry.RookRays,frameF,frameR] at rays
    obtain ⟨_,_,a,v,_,notKing,_,region⟩ := rays
    exact False.elim (eight_no_high_king notKing.symm (by omega) (region_clear notKing.symm region))

theorem four_five_eight_clear {rs : Square} (file : rs.1.val = 4 ∨ rs.1.val = 5) (row : rs.2.val = 1) :
    KRKEightGeometry.Clear (3,2) rs (3,0) := by
  have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
  refine ⟨?_,⟨((2 : Fin 8),0),?_⟩,?_⟩
  · dsimp [SafeRook,dInf,absDiff]
    omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  · intro t guard
    have choices : t = ((2 : Fin 8),0) ∨ t = ((4 : Fin 8),0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases choices with rfl | rfl
    · exact (KRKSevenSecond.clear_iff distinct guard.2.1.symm guard.2.2.2).mpr
        (Or.inr ⟨.east,rfl,True.intro⟩)
    · have five : rs.1.val = 5 := by
        have notCheck := guard.2.2.2
        dsimp [RookSees,RookLine,OnSeg] at notCheck
        omega
      apply (KRKSevenMiddle.low_rook_clear_iff (wk := ((4 : Fin 8),0)) rfl (by decide) (by decide)
        (by omega) distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm
        guard.2.2.1 guard.2.2.2).mpr
      exact ⟨rfl,Or.inr (Or.inl ⟨by decide,by change rs.1.val = 5; exact five⟩)⟩

theorem king_two_three_sufficient {sk rs : Square} (sx : sk.1.val = 2) (sy : sk.2.val = 3)
    (ry : rs.2.val = 1) (file : rs.1.val = 4 ∨ rs.1.val = 5) : KRKNineGeometry.Clear sk rs (3,0) := by
  have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,ry]; dsimp; omega
  have region : KRKEightGlobal.Region (3,2) rs (3,0) :=
    (KRKEightGlobal.edge_clear_iff distinct (by decide)).mp (four_five_eight_clear file ry)
  apply KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) ?_ distinct (by decide) region
  dsimp [dInf,absDiff]
  omega

theorem king_two_three_iff {sk rs : Square} (sx : sk.1.val = 2) (sy : sk.2.val = 3) (ry : rs.2.val = 1) :
    KRKNineGeometry.Clear sk rs (3,0) ↔ rs.1.val = 4 ∨ rs.1.val = 5 :=
  ⟨king_two_three_necessary sx sy ry,king_two_three_sufficient sx sy ry⟩

end EndgameChess.Rules.KRKNineMiddleLow
