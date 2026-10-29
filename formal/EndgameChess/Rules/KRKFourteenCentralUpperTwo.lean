import EndgameChess.Rules.KRKFourteenCentralUpperZero

namespace EndgameChess.Rules.KRKFourteenCentralUpperTwo
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

private theorem near_eight : KRKEightGlobal.Region (3,2) (4,1) (1,0) := by
  change KRKEightEdge.Region (3,2) (4,1) (1,0)
  refine ⟨Or.inl (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]; decide
  · intro i guard
    cases i with
    | west => exact Or.inl ⟨rfl,Or.inr (Or.inr ⟨.highMiddle,rfl,Or.inl (by decide)⟩)⟩
    | east => exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inr ⟨.east,rfl,True.intro⟩⟩))
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) (4,1) (1,0) (KRKEightEdge.destination (1,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]; decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) (4,1) (1,0) (KRKEightEdge.destination (1,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]; decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) (4,1) (1,0) (KRKEightEdge.destination (1,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]; decide
      exact False.elim (absent guard)

private theorem middle_eight : KRKEightGlobal.Region (4,2) (5,1) (3,0) := by
  change KRKEightEdge.Region (4,2) (5,1) (3,0)
  refine ⟨Or.inl (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]; decide
  · intro i guard
    cases i with
    | west => exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inl ⟨.east,Or.inr ⟨rfl,by decide⟩,by decide⟩⟩))
    | east =>
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
      refine ⟨Or.inr rfl,?_⟩
      change KRKFiveMiddle.Five (3,2) (2,1) (3,0)
      exact Or.inr (Or.inl rfl)
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) (5,1) (3,0) (KRKEightEdge.destination (3,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]; decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) (5,1) (3,0) (KRKEightEdge.destination (3,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]; decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((4 : Fin 8),2) (5,1) (3,0) (KRKEightEdge.destination (3,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]; decide
      exact False.elim (absent guard)

private theorem near_nine : KRKNineGeometry.Clear (4,2) (4,1) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by decide) (by decide) near_eight

private theorem middle_nine : KRKNineGeometry.Clear (4,2) (4,1) (3,0) :=
  KRKNineGeometry.rook_step_clear (nr := ((5 : Fin 8),1)) (by dsimp [RookSees,RookLine,OnSeg]; decide)
    (by decide) (by decide) middle_eight

private theorem second_ten : KRKTenGlobal.Region (4,2) (4,1) (2,0) := by
  have clear : KRKTenGeometry.Clear (4,2) (4,1) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl
      · exact near_nine
      · exact middle_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem middle_twelve : KRKTwelveGlobal.Region (5,2) (4,1) (3,0) := by
  have clear : KRKTwelveGeometry.Clear (5,2) (4,1) (3,0) := by
    refine ⟨Or.inr (by decide),⟨((2 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have target : t = ((2 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rw [target]
      exact KRKElevenGeometry.king_step_clear (ns := ((4 : Fin 8),2)) (by decide) (by decide) (by decide) second_ten
  exact (KRKTwelveGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem edge_thirteen {j : Fin 8} (choice : j = 2 ∨ j = 3) : KRKThirteenGeometry.Clear (2,5) (2,4) (0,j) := by
  have source : KRKThirteenGeometry.Clear (5,2) (4,2) (j,0) := by
    rcases choice with rfl | rfl
    · exact KRKThirteenGeometry.king_step_clear (ns := ((4 : Fin 8),1)) (by decide) (by decide) (by decide)
        (KRKFourteenCentralUpperZero.low_second_twelve (by decide))
    · exact KRKThirteenGeometry.rook_step_clear (nr := ((4 : Fin 8),1))
        (by dsimp [RookSees,RookLine,OnSeg]; decide) (by decide) (by decide) middle_twelve
  have mapped := KRKThirteenGeometry.frame_map (Frame.ofSym symSwap) (by decide)
    (by rcases choice with rfl | rfl <;> decide) (by rcases choice with rfl | rfl <;> decide)
    (by rcases choice with rfl | rfl <;> decide)
    (by rcases choice with rfl | rfl <;> dsimp [RookSees,RookLine,OnSeg] <;> decide) source
  simpa only [Frame.ofSym,symSwap] using mapped

theorem clear : KRKFourteenGeometry.Clear ((2 : Fin 8),5) (2,4) (1,3) := by
  refine ⟨Or.inr (by decide),⟨((0 : Fin 8),2),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
  · intro t guard
    have targets : t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
    rcases targets with rfl | rfl | rfl
    · exact edge_thirteen (Or.inl rfl)
    · exact edge_thirteen (Or.inr rfl)
    · have region : KRKTwelveNearExact.Region (1,4) (2,4) :=
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,Or.inr (Or.inl ⟨rfl,by decide⟩)⟩)))
      exact KRKThirteenGeometry.king_step_clear (ns := ((1 : Fin 8),4)) (by decide) (by decide) (by decide)
        (KRKThirteenInteriorBarriers.near_region_iff.mpr region)

end EndgameChess.Rules.KRKFourteenCentralUpperTwo
