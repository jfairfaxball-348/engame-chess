import EndgameChess.Rules.KRKTwelveInnerHighExact

namespace EndgameChess.Rules.KRKTwelveInnerUpperEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private theorem side_corner_seven {r : Fin 8} (width : 2 ≤ r.val) :
    KRKSevenCorner.Seven (3,1) (r,2) := by
  refine Or.inl (Or.inr ⟨.near,by decide,by simp [KRKSevenCorner.king,symSwap],?_,?_,?_⟩)
  · dsimp [KRKSixCorner.Region,KRKSevenCorner.king,symSwap]
    omega
  · refine Or.inl ?_
    simp only [KRKCornerWeakBand.Guard,KRKSevenCorner.king,symSwap,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · exact Or.inl (by dsimp [KRKSevenCorner.king,symSwap,dInf,absDiff]; omega)

theorem low_near_eight {r : Fin 8} (width : 2 ≤ r.val) : KRKEightGlobal.Region (3,1) (r,2) (1,0) := by
  change KRKEightEdge.Region (3,1) (r,2) (1,0)
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨.west,?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,KRKEightEdge.destination,KRKEightEdge.left,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro i guard
    cases i with
    | west => exact Or.inl ⟨rfl,side_corner_seven width⟩
    | east =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),1) (r,2) (1,0) (2,0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff]; dsimp; omega
      exact False.elim (absent guard)
    | northWest =>
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,Or.inl ⟨.middle,?_,by decide,by simp [KRKSevenNear.king,symSwap],?_⟩⟩))))
      · dsimp [KRKSevenNear.RookRegion,symSwap]; omega
      · exact Or.inl (by dsimp [KRKSevenNear.king,symSwap,dInf,absDiff]; omega)
    | north =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact ⟨rfl,Or.inr (Or.inr (Or.inl ⟨rfl,Or.inl rfl⟩))⟩
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),1) (r,2) (1,0) (2,1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff]; dsimp; omega
      exact False.elim (absent guard)

theorem low_near_ten {r : Fin 8} (width : 2 ≤ r.val) : KRKTenGlobal.Region (3,1) (r,2) (1,0) :=
  KRKTwelveNearFileEntries.eight_region_subset (by simp) (by simp) (by decide) (low_near_eight width)

private theorem upper_inner_nine {h : Fin 8} (height : 3 ≤ h.val) : KRKNineGeometry.Clear (1,3) (2,h) (1,1) := by
  apply (KRKNineInner.clear_iff (by simp) (by decide) (by simp) (by decide)
    (by simp only [RookSees,RookLine,OnSeg]; dsimp; omega)).mpr
  exact Or.inr (Or.inr ⟨.side,rfl,Or.inl ⟨by change 2 ≤ 2; decide,by change 2 ≤ 4; decide⟩⟩)

private theorem upper_near_nine {h : Fin 8} (height : 3 ≤ h.val) : KRKNineGeometry.Clear (1,3) (2,h) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide)
    (by simp only [ne_iff_coords]; dsimp; omega) (by decide)
    (KRKEightDiagonalEntries.near_region (by simp only [ne_iff_coords]; dsimp; omega)
      (Or.inl (by dsimp [dInf,absDiff]; omega)))

private theorem upper_corner_nine {h : Fin 8} (height : 3 ≤ h.val) : KRKNineGeometry.Clear (1,3) (2,h) (0,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide)
    (by simp only [ne_iff_coords]; dsimp; omega) (by decide)
    (KRKEightDiagonalEntries.corner_region (by dsimp [dInf,absDiff]; omega))

private theorem upper_west_nine {h : Fin 8} (height : 3 ≤ h.val) : KRKNineGeometry.Clear (1,3) (2,h) (0,1) := by
  let q := krkPos .white (3,1) (h,2) (1,0) .white
  have apart : ((3,1) : Square) ≠ (h,2) := by simp
  have notWeak : ((h,2) : Square) ≠ (1,0) := by simp
  have material : IsKRK q .white (3,1) (h,2) (1,0) := ⟨apart,by decide,notWeak,rfl⟩
  have notCheck : ¬RookSees (h,2) (1,0) (3,1) (1,0) := by
    simp only [RookSees,RookLine,OnSeg]; dsimp; omega
  have seven := KRKSevenGeometry.sufficient material rfl (by decide) notCheck
    ((KRKSevenNear.clear_iff apart notWeak notCheck).mpr (Or.inr ⟨.side,rfl,Or.inl (by change 2 ≤ 2; decide)⟩))
  have nine := KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono seven (by decide))
  have mapped := KRKNineGeometry.frame_map (Frame.ofSym symSwap) apart (by decide) notWeak (by decide) notCheck nine
  simpa only [Frame.ofSym,symSwap] using mapped

theorem upper_corner_ten {h : Fin 8} (height : 3 ≤ h.val) : KRKTenGlobal.Region (1,3) (2,h) (0,0) := by
  have clear : KRKTenGeometry.Clear (1,3) (2,h) (0,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),1),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; dsimp; omega
    · intro t guard
      have targets : t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl
      · exact upper_west_nine height
      · exact upper_near_nine height
      · exact upper_inner_nine height
  exact (KRKTenGlobal.edge_clear_iff (by simp) (by decide)).mp clear

theorem upper_near_ten {h : Fin 8} (height : 3 ≤ h.val) : KRKTenGlobal.Region (1,3) (2,h) (1,0) := by
  have clear : KRKTenGeometry.Clear (1,3) (2,h) (1,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; dsimp; omega
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl
      · exact upper_corner_nine height
      · exact upper_west_nine height
      · exact upper_inner_nine height
  exact (KRKTenGlobal.edge_clear_iff (by simp) (by decide)).mp clear

private theorem middle_nine : KRKNineGeometry.Clear (4,2) (2,2) (3,0) := by
  let q := krkPos .white (4,2) (2,2) (3,0) .white
  have material : IsKRK q .white (4,2) (2,2) (3,0) := ⟨by decide,by decide,by decide,rfl⟩
  have notCheck : ¬RookSees ((2 : Fin 8),2) (3,0) (4,2) (3,0) := by dsimp [RookSees,RookLine,OnSeg]; decide
  have five := KRKFiveGeometry.sufficient material rfl (by decide) notCheck
    ((KRKFiveMiddle.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) (by decide) material.1 material.2.2.1 notCheck).mpr
      (Or.inr (Or.inr (Or.inr ⟨rfl,Or.inl rfl⟩))))
  exact KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono five (by decide))

theorem second_outer_ten {k : Fin 8} (bound : k.val ≤ 2) : KRKTenGlobal.Region (4,k) (2,2) (2,0) := by
  have clear : KRKTenGeometry.Clear (4,k) (2,2) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; dsimp; omega
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) ∨ t = ((3 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl
      · exact KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),1))
          (by dsimp [dInf,absDiff]; omega) (by decide) (by decide) (low_near_eight (by decide))
      · have region : KRKEightGlobal.Region (3,1) (2,2) (1,1) :=
          KRKNineInner.global_region_iff.mpr (Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,by decide⟩⟩)⟩)
        exact KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),1))
          (by dsimp [dInf,absDiff]; omega) (by decide) (by decide) region
      · have kEq : k = 2 := by
          apply Fin.ext
          have far := guard.2.2.1
          dsimp [dInf,absDiff] at far
          omega
        rw [kEq]
        exact middle_nine
  exact (KRKTenGlobal.edge_clear_iff (by simp) (by decide)).mp clear

end EndgameChess.Rules.KRKTwelveInnerUpperEntries
