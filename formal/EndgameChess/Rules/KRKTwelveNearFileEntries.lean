import EndgameChess.Rules.KRKTwelveNearStrip

namespace EndgameChess.Rules.KRKTwelveNearFileEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem eight_region_subset {sk rs wk : Square} (apart : sk ≠ rs) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (region : KRKEightGlobal.Region sk rs wk) : KRKTenGlobal.Region sk rs wk := by
  let q := krkPos .white sk rs wk .black
  have material : IsKRK q .white sk rs wk := ⟨apart,ne_of_dInf_pos (by omega),notRook,rfl⟩
  have eight := (KRKEightGlobal.kernel_eight_iff material rfl far).mpr (Or.inr region)
  have notTerminal : ¬KRKMateGeometry.Terminal sk rs wk := by
    intro terminal
    have mate := (KRKMateGeometry.kernel_mate_iff material rfl far).mpr terminal
    exact mate.2 (KRKEightGlobal.region_live material rfl far region)
  exact ((KRKTenGlobal.kernel_ten_iff material rfl far).mp (mateWithin_mono eight (by decide))).resolve_left notTerminal

private theorem corner_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((4 : Fin 8),1) (0,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.corner_region (by decide))

private theorem near_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((4 : Fin 8),1) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))

private theorem second_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((4 : Fin 8),1) (2,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.second_region (Or.inr (Or.inr ⟨rfl,Or.inr rfl⟩)))

private theorem middle_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((4 : Fin 8),1) (3,0) :=
  KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by decide) (by decide)
    KRKTwelveCentralOppositionEntries.middle_eight

theorem low_ten {j : Fin 8} (low : 1 ≤ j.val) (high : j.val ≤ 2) :
    KRKTenGlobal.Region ((2 : Fin 8),3) ((4 : Fin 8),1) (j,0) := by
  let x : Fin 8 := ⟨j.val-1,by omega⟩
  have clear : KRKTenGeometry.Clear ((2 : Fin 8),3) ((4 : Fin 8),1) (j,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨(x,0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp [x]
      simp <;> omega
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨
          t = ((2 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl | rfl
      · exact corner_nine
      · exact near_nine
      · exact second_nine
      · exact middle_nine
  have edge : KRKEdgeDepth.depth (j,0) = 0 := by dsimp [KRKEdgeDepth.depth]; omega
  simp only [KRKTenGlobal.Region,edge,↓reduceIte]
  exact (KRKTenGlobal.edge_clear_iff (by decide) edge).mp clear

private theorem diagonal_ten {j : Fin 8} (choice : j = 1 ∨ j = 2) :
    KRKTenGlobal.Region ((2 : Fin 8),2) ((4 : Fin 8),1) (j,0) := by
  rcases choice with rfl | rfl
  · exact eight_region_subset (by decide) (by decide) (by decide)
      (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))
  · exact eight_region_subset (by decide) (by decide) (by decide)
      (KRKEightDiagonalEntries.second_region (Or.inr (Or.inr ⟨rfl,Or.inr rfl⟩)))

theorem low_eleven {rs : Square} {j : Fin 8} (ry : rs.2.val = 1) (choice : j = 1 ∨ j = 2) :
    KRKElevenGeometry.Clear ((2 : Fin 8),3) rs (j,0) := by
  by_cases four : rs.1.val = 4
  · have equal : rs = ((4 : Fin 8),1) := Prod.ext (Fin.ext four) (Fin.ext ry)
    rw [equal]
    apply KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) ?_ (diagonal_ten choice)
    rcases choice with rfl | rfl <;> decide
  · have sees : RookSees rs ((4 : Fin 8),1) (2,3) (j,0) := by
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords,ry]
      simp <;> omega
    have notWeak : ((4,1) : Square) ≠ (j,0) := by simp [ne_iff_coords]
    have bounds : 1 ≤ j.val ∧ j.val ≤ 2 := by rcases choice with rfl | rfl <;> decide
    exact KRKElevenGeometry.rook_step_clear sees (by decide) notWeak (low_ten bounds.1 bounds.2)

theorem middle_eleven {rs : Square} (ry : rs.2.val = 1) (notThree : rs.1.val ≠ 3) :
    KRKElevenGeometry.Clear ((2 : Fin 8),3) rs (3,0) := by
  have apart : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,ry]; dsimp; omega
  exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) apart (by decide)
    (KRKTwelveCentralOppositionEntries.middle_ten ry notThree)

end EndgameChess.Rules.KRKTwelveNearFileEntries
