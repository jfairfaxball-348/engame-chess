import EndgameChess.Rules.KRKFourteenCentralNecessary

namespace EndgameChess.Rules.KRKFourteenCentralUpperZero
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem ten_inner_side {r : Fin 8} (width : 4 ≤ r.val) : KRKTenGlobal.Region (3,1) (r,2) (1,1) := by
  apply KRKElevenInner.global_region_iff.mpr
  exact Or.inl (Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,by change 2 ≤ r.val; omega⟩⟩)⟩)

private theorem low_near_transposed {r : Fin 8} (width : 4 ≤ r.val) : KRKElevenGeometry.Clear (4,1) (r,2) (2,1) := by
  have source : KRKElevenGeometry.Clear (1,4) (2,r) (1,2) :=
    (KRKElevenNearStrip.clear_iff (by simp) (by simp)).mpr (Or.inr ⟨.upperOne,rfl,Or.inl rfl⟩)
  have mapped := KRKElevenGeometry.frame_map (Frame.ofSym symSwap) (by simp) (by decide) (by simp) (by decide)
    (by simp only [RookSees,RookLine,OnSeg]; dsimp; omega) source
  simpa only [Frame.ofSym,symSwap] using mapped

theorem low_second_twelve {r : Fin 8} (width : 4 ≤ r.val) : KRKTwelveGlobal.Region (4,1) (r,2) (2,0) := by
  have clear : KRKTwelveGeometry.Clear (4,1) (r,2) (2,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; dsimp; omega
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl
      · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1)) (by decide) (by simp) (by decide)
          (KRKTwelveInnerUpperEntries.low_near_ten (by omega))
      · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1)) (by decide) (by simp) (by decide) (ten_inner_side width)
      · exact low_near_transposed width
  exact (KRKTwelveGlobal.edge_clear_iff (by simp) (by decide)).mp clear

private theorem low_near_nine {r : Fin 8} (width : 5 ≤ r.val) : KRKNineGeometry.Clear (4,0) (r,1) (1,0) := by
  let q := krkPos .white (4,0) (r,1) (1,0) .white
  have apart : ((4,0) : Square) ≠ (r,1) := by simp
  have notWeak : ((r,1) : Square) ≠ (1,0) := by simp
  have material : IsKRK q .white (4,0) (r,1) (1,0) := ⟨apart,by decide,notWeak,rfl⟩
  have notCheck : ¬RookSees (r,1) (1,0) (4,0) (1,0) := by simp only [RookSees,RookLine,OnSeg]; dsimp; omega
  have seven := KRKSevenGeometry.sufficient material rfl (by decide) notCheck
    ((KRKSevenNear.clear_iff apart notWeak notCheck).mpr
      (Or.inl ⟨.low,Or.inl ⟨rfl,by change 3 ≤ r.val; omega⟩,by decide,by simp [KRKSevenNear.king],
        Or.inl (by dsimp [dInf,absDiff]; omega)⟩))
  exact KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono seven (by decide))

private theorem low_second_ten {r : Fin 8} (width : 5 ≤ r.val) : KRKTenGlobal.Region (4,0) (r,1) (2,0) := by
  have clear : KRKTenGeometry.Clear (4,0) (r,1) (2,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; dsimp; omega
    · intro t guard
      have target : t = ((1 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rw [target]
      exact low_near_nine width
  exact (KRKTenGlobal.edge_clear_iff (by simp) (by decide)).mp clear

private theorem low_middle_twelve {r : Fin 8} (width : 5 ≤ r.val) : KRKTwelveGlobal.Region (5,0) (r,1) (3,0) := by
  have clear : KRKTwelveGeometry.Clear (5,0) (r,1) (3,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((2 : Fin 8),0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; dsimp; omega
    · intro t guard
      have target : t = ((2 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rw [target]
      exact KRKElevenGeometry.king_step_clear (ns := ((4 : Fin 8),0)) (by decide) (by simp) (by decide) (low_second_ten width)
  exact (KRKTwelveGlobal.edge_clear_iff (by simp) (by decide)).mp clear

private theorem zero_edge_thirteen {r j : Fin 8} (height : 5 ≤ r.val) (choice : j = 2 ∨ j = 3) :
    KRKThirteenGeometry.Clear (0,5) (2,r) (0,j) := by
  have source : KRKThirteenGeometry.Clear (5,0) (r,2) (j,0) := by
    rcases choice with rfl | rfl
    · exact KRKThirteenGeometry.king_step_clear (ns := ((4 : Fin 8),1)) (by decide) (by simp) (by decide) (low_second_twelve (by omega))
    · exact KRKThirteenGeometry.rook_step_clear (nr := (r,(1 : Fin 8)))
        (by simp [RookSees,RookLine,OnSeg,show ((5 : Fin 8).val) = 5 from rfl]) (by simp) (by simp) (low_middle_twelve height)
  have mapped := KRKThirteenGeometry.frame_map (Frame.ofSym symSwap) (by simp) (by rcases choice with rfl | rfl <;> decide) (by simp)
    (by rcases choice with rfl | rfl <;> decide)
    (by simp only [RookSees,RookLine,OnSeg]; dsimp; rcases choice with rfl | rfl <;> omega) source
  simpa only [Frame.ofSym,symSwap] using mapped

theorem clear {r : Fin 8} (height : 5 ≤ r.val) : KRKFourteenGeometry.Clear (0,5) (2,r) (1,3) := by
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),2),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; dsimp; omega
  · intro t guard
    have targets : t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
    rcases targets with rfl | rfl | rfl
    · exact zero_edge_thirteen height (Or.inl rfl)
    · exact zero_edge_thirteen height (Or.inr rfl)
    · have region : KRKTwelveNearExact.Region (1,4) (2,r) :=
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,Or.inr (Or.inl ⟨rfl,by change 3 ≤ r.val; omega⟩)⟩)))
      exact KRKThirteenGeometry.king_step_clear (ns := ((1 : Fin 8),4)) (by decide) (by simp) (by decide)
        (KRKThirteenInteriorBarriers.near_region_iff.mpr region)

end EndgameChess.Rules.KRKFourteenCentralUpperZero
