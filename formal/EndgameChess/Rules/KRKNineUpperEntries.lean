import EndgameChess.Rules.KRKNineSecondBoundary

namespace EndgameChess.Rules.KRKNineUpperEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem near_side_eight {rs : Square} (width : 3 ≤ rs.1.val) (row : rs.2.val = 2) :
    KRKEightGeometry.Clear (3,1) rs (1,0) := by
  have distinct : ((3 : Fin 8),1) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
  refine ⟨Or.inl ?_,⟨((1 : Fin 8),1),?_⟩,?_⟩
  · dsimp [dInf,absDiff]; omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  · intro t guard
    have choices : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),1) := by
      have distance := guard.1
      have far := guard.2.2.1
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp [dInf,absDiff] at distance far
      dsimp
      omega
    rcases choices with rfl | rfl | rfl
    · apply (KRKSevenCorner.clear_iff distinct (by decide) guard.2.1.symm guard.2.2.1 guard.2.2.2).mpr
      exact Or.inr (Or.inr ⟨.highNear,rfl,Or.inr (by change 2 ≤ rs.2.val; omega)⟩)
    · apply (KRKEightEdge.seven_test_iff distinct (by decide) guard.2.1.symm guard.2.2.1 guard.2.2.2
        (by decide) (by decide)).mpr
      have near : KRKSevenNear.Seven (symSwap.f ((3 : Fin 8),1)) (symSwap.f rs) := by
        refine Or.inl ⟨.diagonal,True.intro,by decide,?_,Or.inl ?_⟩
        · simp only [KRKSevenNear.king,symSwap,ne_iff_coords,row]; dsimp; omega
        · dsimp [KRKSevenNear.king,symSwap,dInf,absDiff]; omega
      simpa [KRKEightEdge.SevenTest,KRKSevenNear.Seven] using near
    · apply (KRKSevenInner.clear_iff distinct (by decide) guard.2.1.symm guard.2.2.1 guard.2.2.2).mpr
      exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inl row⟩))

private theorem second_far_eight {rs : Square} (width : 3 ≤ rs.1.val) (row : rs.2.val = 1) :
    KRKEightGeometry.Clear (4,0) rs (2,0) := by
  have distinct : ((4 : Fin 8),0) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
  refine ⟨?_,⟨((1 : Fin 8),0),?_⟩,?_⟩
  · dsimp [SafeRook,dInf,absDiff]; omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  · intro t guard
    have target : t = ((1 : Fin 8),0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    subst t
    apply (KRKSevenNear.clear_iff distinct guard.2.1.symm guard.2.2.2).mpr
    refine Or.inl ⟨.low,Or.inl ⟨row,width⟩,by decide,?_,Or.inl ?_⟩
    · simp only [KRKSevenNear.king,ne_iff_coords,row]; dsimp; omega
    · dsimp [KRKSevenNear.king,dInf,absDiff]; omega

private theorem second_protected_eight : KRKEightGeometry.Clear ((4 : Fin 8),1) ((3 : Fin 8),1) (2,0) := by
  refine ⟨Or.inr (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
  · simp [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] <;> omega
  · intro t guard
    have target : t = ((1 : Fin 8),0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    subst t
    apply (KRKSevenNear.clear_iff (by decide) guard.2.1.symm guard.2.2.2).mpr
    refine Or.inl ⟨.low,Or.inl ⟨rfl,by decide⟩,by decide,by decide,Or.inl (by decide)⟩

private theorem second_side_eight {rs : Square} (width : 4 ≤ rs.1.val) (row : rs.2.val = 2) :
    KRKEightGeometry.Clear (3,2) rs (2,0) := by
  have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
  refine ⟨Or.inl ?_,⟨((1 : Fin 8),0),?_⟩,?_⟩
  · dsimp [dInf,absDiff]; omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  · intro t guard
    have choices : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases choices with rfl | rfl | rfl
    · apply (KRKSevenNear.clear_iff distinct guard.2.1.symm guard.2.2.2).mpr
      refine Or.inl ⟨.diagonal,True.intro,by decide,?_,Or.inl ?_⟩
      · simp only [KRKSevenNear.king,ne_iff_coords,row]; dsimp; omega
      · dsimp [KRKSevenNear.king,dInf,absDiff]; omega
    · apply (KRKSevenMiddle.bottom_clear_iff rfl (by decide) (by decide) distinct (by decide)
        guard.2.1.symm guard.2.2.1 guard.2.2.2).mpr
      change KRKFiveMiddle.Five (3,2) rs (3,0)
      exact Or.inr (Or.inl rfl)
    · apply (KRKSevenInner.clear_iff distinct (by decide) guard.2.1.symm guard.2.2.1 guard.2.2.2).mpr
      exact Or.inl ⟨row,by omega,by decide⟩

private theorem to_region {sk rs wk : Square} (distinct : sk ≠ rs) (edge : KRKEdgeDepth.depth wk = 0)
    (clear : KRKEightGeometry.Clear sk rs wk) : KRKEightGlobal.Region sk rs wk := by
  simp only [KRKEightGlobal.Region,edge,↓reduceIte]
  exact (KRKEightGlobal.edge_clear_iff distinct edge).mp clear

theorem near_entry {sk rs : Square} (sx : sk.1.val = 4) (sy : sk.2.val = 0 ∨ sk.2.val = 1)
    (width : 3 ≤ rs.1.val) (row : rs.2.val = 2) : KRKNineGeometry.Clear sk rs (1,0) := by
  have distinct : ((3 : Fin 8),1) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
  have region := to_region distinct (by decide) (near_side_eight width row)
  apply KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),1)) ?_ distinct (by decide) region
  dsimp [dInf,absDiff]
  omega

theorem second_entry {sk rs : Square} (sx : sk.1.val = 4) (sy : sk.2.val = 0 ∨ sk.2.val = 1)
    (width : 3 ≤ rs.1.val) (row : rs.2.val = 2) : KRKNineGeometry.Clear sk rs (2,0) := by
  rcases sy with zero | one
  · have king : sk = ((4 : Fin 8),0) := Prod.ext (Fin.ext sx) (Fin.ext zero)
    rw [king]
    let nr : Square := (rs.1,1)
    have nrRow : nr.2.val = 1 := rfl
    have distinct : ((4 : Fin 8),0) ≠ nr := by simp only [ne_iff_coords,nrRow]; dsimp; omega
    have region := to_region distinct (by decide) (second_far_eight (rs := nr) width nrRow)
    apply KRKNineGeometry.rook_step_clear (nr := nr) ?_ distinct.symm ?_ region
    · simp only [nr,RookSees,RookLine,OnSeg,ne_iff_coords,row]; simp <;> omega
    · simp only [nr,ne_iff_coords]; dsimp; omega
  · by_cases three : rs.1.val = 3
    · have king : sk = ((4 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext one)
      have rook : rs = ((3 : Fin 8),2) := Prod.ext (Fin.ext three) (Fin.ext row)
      rw [king,rook]
      apply KRKNineGeometry.rook_step_clear (nr := ((3 : Fin 8),1))
      · simp [RookSees,RookLine,OnSeg]
      · decide
      · decide
      · exact to_region (by decide) (by decide) second_protected_eight
    · have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
      have region := to_region distinct (by decide) (second_side_eight (by omega) row)
      apply KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) ?_ distinct (by decide) region
      dsimp [dInf,absDiff]
      omega

end EndgameChess.Rules.KRKNineUpperEntries
