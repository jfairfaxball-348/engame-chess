import EndgameChess.Rules.KRKTwelveNearFileOne

namespace EndgameChess.Rules.KRKTwelveNearNewEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem near_eight : KRKEightGlobal.Region ((3 : Fin 8),2) ((3 : Fin 8),1) (1,0) := by
  change KRKEightEdge.Region ((3 : Fin 8),2) ((3 : Fin 8),1) (1,0)
  refine ⟨Or.inl (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]
    decide
  · intro i guard
    cases i with
    | west => exact Or.inl ⟨rfl,Or.inr (Or.inr ⟨.highMiddle,rfl,Or.inl (by decide)⟩)⟩
    | east => exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inr ⟨.east,rfl,True.intro⟩⟩))
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) ((3 : Fin 8),1) (1,0)
          (KRKEightEdge.destination (1,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) ((3 : Fin 8),1) (1,0)
          (KRKEightEdge.destination (1,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) ((3 : Fin 8),1) (1,0)
          (KRKEightEdge.destination (1,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)

private theorem upper_near_nine : KRKNineGeometry.Clear ((4 : Fin 8),2) ((3 : Fin 8),1) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by decide) (by decide) near_eight

private theorem low_corner_nine : KRKNineGeometry.Clear ((3 : Fin 8),1) ((3 : Fin 8),2) (0,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.corner_region (by decide))

private theorem low_west_nine : KRKNineGeometry.Clear ((3 : Fin 8),1) ((3 : Fin 8),2) (0,1) := by
  let g := Frame.ofSym symSwap
  have mapped : KRKNineGeometry.Clear ((1 : Fin 8),3) ((2 : Fin 8),3) (1,0) :=
    KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
      (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))
  have back := KRKNineGeometry.frame_map g (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide) mapped
  simpa only [g,Frame.ofSym,symSwap] using back

private theorem low_inner_nine : KRKNineGeometry.Clear ((3 : Fin 8),1) ((3 : Fin 8),2) (1,1) := by
  apply (KRKNineInner.clear_iff (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
  exact Or.inr (Or.inl ⟨.side,rfl,Or.inl ⟨by decide,by decide⟩⟩)

private theorem high_corner_nine : KRKNineGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),3) (0,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.corner_region (by decide))

private theorem high_west_nine : KRKNineGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),3) (0,1) := by
  let g := Frame.ofSym symSwap
  have mapped : KRKNineGeometry.Clear ((2 : Fin 8),3) ((3 : Fin 8),2) (1,0) :=
    KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
      (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))
  have back := KRKNineGeometry.frame_map g (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide) mapped
  simpa only [g,Frame.ofSym,symSwap] using back

private theorem high_inner_nine : KRKNineGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),3) (1,1) := by
  apply (KRKNineInner.clear_iff (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
  exact Or.inr (Or.inl ⟨.high,rfl,Or.inl (by decide)⟩)

theorem low_near_ten : KRKTenGlobal.Region ((3 : Fin 8),1) ((3 : Fin 8),2) (1,0) := by
  have clear : KRKTenGeometry.Clear ((3 : Fin 8),1) ((3 : Fin 8),2) (1,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · exact low_corner_nine
      · exact low_west_nine
      · exact low_inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

theorem upper_second_ten : KRKTenGlobal.Region ((4 : Fin 8),2) ((3 : Fin 8),1) (2,0) := by
  have clear : KRKTenGeometry.Clear ((4 : Fin 8),2) ((3 : Fin 8),1) (2,0) := by
    refine ⟨Or.inr (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    · intro t guard
      have target : t = ((1 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rw [target]
      exact upper_near_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

theorem high_near_ten : KRKTenGlobal.Region ((3 : Fin 8),2) ((2 : Fin 8),3) (1,0) := by
  have clear : KRKTenGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),3) (1,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · exact high_corner_nine
      · exact high_west_nine
      · exact high_inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

theorem upper_low_eleven {j : Fin 8} (choice : j = 1 ∨ j = 2) :
    KRKElevenGeometry.Clear ((4 : Fin 8),2) ((3 : Fin 8),2) (j,0) := by
  rcases choice with rfl | rfl
  · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1))
      (by decide) (by decide) (by decide) low_near_ten
  · exact KRKElevenGeometry.rook_step_clear
      (by dsimp [RookSees,RookLine,OnSeg]; decide) (by decide) (by decide) upper_second_ten

theorem row_near_eleven {k : Fin 8} (choice : k = 1 ∨ k = 2) :
    KRKElevenGeometry.Clear ((4 : Fin 8),k) ((2 : Fin 8),3) (1,0) := by
  apply KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) ?_ (by decide) (by decide) high_near_ten
  rcases choice with rfl | rfl <;> decide

theorem row_middle_eleven {k : Fin 8} (choice : k = 1 ∨ k = 2) :
    KRKElevenGeometry.Clear ((4 : Fin 8),k) ((2 : Fin 8),3) (3,0) := by
  have region := KRKTwelveNearFileEntries.eight_region_subset (by decide) (by decide) (by decide)
    (KRKTwelveCentralEntries.middle_eight_region (rs := ((2 : Fin 8),3)) (by decide))
  apply KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) ?_ (by decide) (by decide) region
  rcases choice with rfl | rfl <;> decide

theorem row_lower_eleven {k : Fin 8} (choice : k = 1 ∨ k = 2) :
    KRKElevenGeometry.Clear ((4 : Fin 8),k) ((2 : Fin 8),3) (1,2) := by
  have region : KRKTenGlobal.Region ((3 : Fin 8),2) ((2 : Fin 8),3) (1,2) := by
    change KRKTenInteriorExact.Region ((3 : Fin 8),2) ((2 : Fin 8),3) (1,2)
    exact ⟨rfl,Or.inr ⟨rfl,Or.inr (Or.inl ⟨rfl,rfl,rfl,by decide⟩)⟩⟩
  apply KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) ?_ (by decide) (by decide) region
  rcases choice with rfl | rfl <;> decide

theorem row_inner_eleven {k : Fin 8} (choice : k = 1 ∨ k = 2) :
    KRKElevenGeometry.Clear (k,(4 : Fin 8)) ((3 : Fin 8),2) (1,1) := by
  have region : KRKTenGlobal.Region ((1 : Fin 8),3) ((3 : Fin 8),2) (1,1) := by
    change KRKTenInteriorExact.Region ((1 : Fin 8),3) ((3 : Fin 8),2) (1,1)
    refine ⟨rfl,Or.inl ⟨rfl,Or.inr (Or.inr (Or.inl ?_))⟩⟩
    exact ⟨rfl,rfl,Or.inl rfl⟩
  apply KRKElevenGeometry.king_step_clear (ns := ((1 : Fin 8),3)) ?_ (by decide) (by decide) region
  rcases choice with rfl | rfl <;> decide

theorem upper_inner_eleven : KRKElevenGeometry.Clear ((2 : Fin 8),4) ((2 : Fin 8),3) (1,1) := by
  have region : KRKTenGlobal.Region ((1 : Fin 8),3) ((2 : Fin 8),3) (1,1) := by
    change KRKTenInteriorExact.Region ((1 : Fin 8),3) ((2 : Fin 8),3) (1,1)
    refine ⟨rfl,Or.inl ⟨rfl,Or.inr (Or.inr (Or.inl ?_))⟩⟩
    exact ⟨rfl,rfl,Or.inr (Or.inr ⟨rfl,by decide⟩)⟩
  exact KRKElevenGeometry.king_step_clear (ns := ((1 : Fin 8),3)) (by decide) (by decide) (by decide) region

end EndgameChess.Rules.KRKTwelveNearNewEntries
