import EndgameChess.Rules.KRKTwelveCentralUpper

namespace EndgameChess.Rules.KRKTwelveCentralOppositionEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem middle_eight : KRKEightGlobal.Region ((3 : Fin 8),2) ((4 : Fin 8),1) (3,0) := by
  change KRKEightEdge.Region ((3 : Fin 8),2) ((4 : Fin 8),1) (3,0)
  refine ⟨Or.inr (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]
    decide
  · intro i guard
    cases i with
    | west => exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inr ⟨.east,rfl,True.intro⟩⟩))
    | east =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) ((4 : Fin 8),1) (3,0)
          (KRKEightEdge.destination (3,0) .east) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northWest =>
      have far := guard.2.2.1
      change 2 ≤ dInf ((3 : Fin 8),2) (2,1) at far
      contradiction
    | north =>
      have far := guard.2.2.1
      change 2 ≤ dInf ((3 : Fin 8),2) (3,1) at far
      contradiction
    | northEast =>
      have far := guard.2.2.1
      change 2 ≤ dInf ((3 : Fin 8),2) (4,1) at far
      contradiction

private theorem near_nine : KRKNineGeometry.Clear ((3 : Fin 8),3) ((4 : Fin 8),1) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))

private theorem middle_nine : KRKNineGeometry.Clear ((3 : Fin 8),3) ((4 : Fin 8),1) (3,0) :=
  KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by decide) (by decide) middle_eight

theorem second_ten : KRKTenGlobal.Region ((3 : Fin 8),3) ((4 : Fin 8),1) (2,0) := by
  have clear : KRKTenGeometry.Clear ((3 : Fin 8),3) ((4 : Fin 8),1) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl
      · exact near_nine
      · exact middle_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

theorem second_eleven {rs : Square} (ry : rs.2.val = 1) (notFour : rs.1.val ≠ 4) :
    KRKElevenGeometry.Clear ((3 : Fin 8),3) rs (2,0) := by
  have sees : RookSees rs ((4 : Fin 8),1) (3,3) (2,0) := by
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,ry]
    simp <;> omega
  exact KRKElevenGeometry.rook_step_clear sees (by decide) (by decide) second_ten

private theorem second_nine_low_row {rs : Square} (ry : rs.2.val = 1)
    (notCheck : ¬RookSees rs (2,0) (3,2) (2,0)) : KRKNineGeometry.Clear ((3 : Fin 8),2) rs (2,0) := by
  let q := krkPos .white (3,2) rs (2,0) .white
  have apart : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,ry]; dsimp; omega
  have notWeak : rs ≠ ((2 : Fin 8),0) := by simp only [ne_iff_coords,ry]; dsimp; omega
  have material : IsKRK q .white (3,2) rs (2,0) := ⟨apart,by decide,notWeak,rfl⟩
  have seven := (KRKSevenSecond.kernel_seven_iff material rfl (by decide) notCheck).mpr
    (Or.inr ⟨.east,rfl,True.intro⟩)
  exact KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono seven (by decide))

private theorem middle_nine_low_row {rs : Square} (ry : rs.2.val = 1) (notFour : rs.1.val ≠ 4) :
    KRKNineGeometry.Clear ((4 : Fin 8),2) rs (3,0) := by
  have sees : RookSees rs ((4 : Fin 8),1) (4,2) (3,0) := by
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,ry]
    simp <;> omega
  exact KRKNineGeometry.rook_step_clear sees (by decide) (by decide) KRKTwelveCentralUpperEntries.middle_eight

theorem middle_ten {rs : Square} (ry : rs.2.val = 1) (notThree : rs.1.val ≠ 3) :
    KRKTenGlobal.Region ((3 : Fin 8),2) rs (3,0) := by
  let x : Fin 8 := if rs.1.val = 2 then 4 else 2
  have width : (x.val = 2 ∨ x.val = 4) ∧ x.val ≠ rs.1.val := by dsimp [x]; split <;> (try simp_all) <;> omega
  have safe : SafeRook ((3 : Fin 8),2) rs (3,0) := by dsimp [SafeRook,dInf,absDiff]; omega
  have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,ry]; dsimp; omega
  have clear : KRKTenGeometry.Clear ((3 : Fin 8),2) rs (3,0) := by
    refine ⟨safe,⟨(x,0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
      simp <;> omega
    · intro t guard
      have targets : t = ((2 : Fin 8),0) ∨ t = ((4 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl
      · exact second_nine_low_row ry guard.2.2.2
      · let g := Frame.ofSym symX
        have mapped : KRKNineGeometry.Clear (g.f ((3 : Fin 8),2)) (g.f rs) (g.f ((4 : Fin 8),0)) :=
          middle_nine_low_row ry (by dsimp [g,Frame.ofSym,symX]; omega)
        have back := KRKNineGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
          (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
          (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
          (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
        simpa only [Frame.inverse,g.left_inv] using back
  exact (KRKTenGlobal.edge_clear_iff distinct (by decide)).mp clear

theorem middle_eleven {rs : Square} (ry : rs.2.val = 1) (notThree : rs.1.val ≠ 3) :
    KRKElevenGeometry.Clear ((3 : Fin 8),3) rs (3,0) := by
  have apart : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,ry]; dsimp; omega
  exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2))
    (by decide) apart (by decide) (middle_ten ry notThree)

theorem high_eleven {rs : Square} (ry : rs.2.val = 1) (notFour : rs.1.val ≠ 4) :
    KRKElevenGeometry.Clear ((3 : Fin 8),3) rs (4,0) := by
  let g := Frame.ofSym symX
  have region : KRKTenGlobal.Region ((3 : Fin 8),2) (g.f rs) (3,0) :=
    middle_ten ry (by dsimp [g,Frame.ofSym,symX]; omega)
  have apart : ((3 : Fin 8),2) ≠ g.f rs := by
    simp only [ne_iff_coords]
    dsimp [g,Frame.ofSym,symX]
    omega
  have mapped : KRKElevenGeometry.Clear (g.f ((3 : Fin 8),3)) (g.f rs) (g.f ((4 : Fin 8),0)) :=
    KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) apart (by decide) region
  have distinct : ((3 : Fin 8),3) ≠ rs := by simp [ne_iff_coords,ry,show ((3 : Fin 8).val) = 3 from rfl]
  have notRook : rs ≠ ((4 : Fin 8),0) := by simp only [ne_iff_coords,ry]; dsimp; omega
  have notCheck : ¬RookSees rs (4,0) (3,3) (4,0) := by
    simp only [RookSees,RookLine,OnSeg,ry]
    dsimp
    omega
  have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
    (g.ne_iff.mpr (by decide)) (g.ne_iff.mpr notRook) (by rw [g.distance]; decide)
    (fun h => notCheck ((g.sees _ _ _ _).mp h)) mapped
  simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKTwelveCentralOppositionEntries
