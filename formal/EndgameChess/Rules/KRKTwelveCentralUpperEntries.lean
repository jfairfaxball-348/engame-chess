import EndgameChess.Rules.KRKElevenEdgeBoundary

namespace EndgameChess.Rules.KRKTwelveCentralUpperEntries
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem corner_seven : KRKSevenCorner.Seven ((4 : Fin 8),2) ((4 : Fin 8),1) := by
  refine Or.inl (Or.inr ⟨.highMiddle,?_⟩)
  refine ⟨by decide,by decide,?_,?_,Or.inl (by decide)⟩
  · dsimp [KRKSixCorner.Region,KRKSevenCorner.king,symSwap]
    decide
  · refine Or.inr (Or.inl ?_)
    dsimp [KRKCornerWeakBand.Guard,KRKSevenCorner.king,symSwap,RookSees,RookLine,OnSeg]
    decide

private theorem second_seven : KRKSevenSecond.Seven ((4 : Fin 8),2) ((4 : Fin 8),1) := by
  exact Or.inl ⟨.east,Or.inr ⟨rfl,by decide⟩,by decide⟩

private theorem near_seven : KRKSevenNear.Seven ((4 : Fin 8),0) ((4 : Fin 8),1) := by
  refine Or.inl ⟨.low,Or.inl ⟨rfl,by decide⟩,by decide,by decide,Or.inl (by decide)⟩

theorem near_eight : KRKEightGlobal.Region ((4 : Fin 8),2) ((4 : Fin 8),1) (1,0) := by
  change KRKEightEdge.Region ((4 : Fin 8),2) ((4 : Fin 8),1) (1,0)
  refine ⟨Or.inl (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]
    decide
  · intro i guard
    cases i with
    | west => exact Or.inl ⟨rfl,corner_seven⟩
    | east => exact Or.inr (Or.inr (Or.inl ⟨rfl,second_seven⟩))
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) ((4 : Fin 8),1) (1,0)
          (KRKEightEdge.destination (1,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) ((4 : Fin 8),1) (1,0)
          (KRKEightEdge.destination (1,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) ((4 : Fin 8),1) (1,0)
          (KRKEightEdge.destination (1,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)

theorem middle_eight : KRKEightGlobal.Region ((4 : Fin 8),2) ((4 : Fin 8),1) (3,0) := by
  change KRKEightEdge.Region ((4 : Fin 8),2) ((4 : Fin 8),1) (3,0)
  refine ⟨Or.inr (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]
    decide
  · intro i guard
    cases i with
    | west => exact Or.inr (Or.inr (Or.inl ⟨rfl,second_seven⟩))
    | east =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) ((4 : Fin 8),1) (3,0)
          (KRKEightEdge.destination (3,0) .east) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) ((4 : Fin 8),1) (3,0)
          (KRKEightEdge.destination (3,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) ((4 : Fin 8),1) (3,0)
          (KRKEightEdge.destination (3,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) ((4 : Fin 8),1) (3,0)
          (KRKEightEdge.destination (3,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)

theorem second_eight : KRKEightGlobal.Region ((4 : Fin 8),0) ((4 : Fin 8),1) (2,0) := by
  change KRKEightEdge.Region ((4 : Fin 8),0) ((4 : Fin 8),1) (2,0)
  refine ⟨Or.inl (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]
    decide
  · intro i guard
    cases i with
    | west => exact Or.inr (Or.inl ⟨rfl,near_seven⟩)
    | east =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),0) ((4 : Fin 8),1) (2,0)
          (KRKEightEdge.destination (2,0) .east) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),0) ((4 : Fin 8),1) (2,0)
          (KRKEightEdge.destination (2,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),0) ((4 : Fin 8),1) (2,0)
          (KRKEightEdge.destination (2,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),0) ((4 : Fin 8),1) (2,0)
          (KRKEightEdge.destination (2,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)

private theorem near_nine : KRKNineGeometry.Clear ((5 : Fin 8),1) ((4 : Fin 8),1) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((4 : Fin 8),2)) (by decide) (by decide) (by decide) near_eight

private theorem second_nine : KRKNineGeometry.Clear ((5 : Fin 8),1) ((4 : Fin 8),1) (2,0) :=
  KRKNineGeometry.king_step_clear (ns := ((4 : Fin 8),0)) (by decide) (by decide) (by decide) second_eight

private theorem middle_nine : KRKNineGeometry.Clear ((5 : Fin 8),1) ((4 : Fin 8),1) (3,0) :=
  KRKNineGeometry.king_step_clear (ns := ((4 : Fin 8),2)) (by decide) (by decide) (by decide) middle_eight

theorem ten_edge_region {j : Fin 8} (low : 2 ≤ j.val) (high : j.val ≤ 4) :
    KRKTenGlobal.Region ((5 : Fin 8),1) ((4 : Fin 8),1) (j,0) := by
  let x : Fin 8 := ⟨j.val-1,by omega⟩
  have clear : KRKTenGeometry.Clear ((5 : Fin 8),1) ((4 : Fin 8),1) (j,0) := by
    refine ⟨Or.inr (by decide),⟨(x,0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp [x]
      simp <;> omega
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · exact near_nine
      · exact second_nine
      · exact middle_nine
  have edge : KRKEdgeDepth.depth (j,0) = 0 := by dsimp [KRKEdgeDepth.depth]; omega
  simp only [KRKTenGlobal.Region,edge,↓reduceIte]
  exact (KRKTenGlobal.edge_clear_iff (by decide) edge).mp clear

theorem edge_eleven {j : Fin 8} (low : 2 ≤ j.val) (high : j.val ≤ 4) :
    KRKElevenGeometry.Clear ((5 : Fin 8),1) ((4 : Fin 8),2) (j,0) := by
  have sees : RookSees ((4 : Fin 8),2) ((4 : Fin 8),1) (5,1) (j,0) := by
    dsimp [RookSees,RookLine,OnSeg]
    omega
  exact KRKElevenGeometry.rook_step_clear sees (by decide) (by simp) (ten_edge_region low high)

end EndgameChess.Rules.KRKTwelveCentralUpperEntries
