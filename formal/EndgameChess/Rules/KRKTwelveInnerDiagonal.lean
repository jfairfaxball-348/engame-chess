import EndgameChess.Rules.KRKTwelveInner

namespace EndgameChess.Rules.KRKTwelveInnerDiagonal
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem corner_eight : KRKEightGlobal.Region ((1 : Fin 8),2) ((2 : Fin 8),2) (0,0) := by
  change KRKEightEdge.Region ((1 : Fin 8),2) ((2 : Fin 8),2) (0,0)
  refine ⟨Or.inl (by decide),⟨.east,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
    decide
  · intro i guard
    cases i with
    | west =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (0,0)
          (KRKEightEdge.destination (0,0) .west) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | east => exact Or.inr (Or.inl ⟨rfl,Or.inr ⟨.middle,rfl,True.intro⟩⟩)
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (0,0)
          (KRKEightEdge.destination (0,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (0,0)
          (KRKEightEdge.destination (0,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (0,0)
          (KRKEightEdge.destination (0,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)

private theorem near_eight : KRKEightGlobal.Region ((1 : Fin 8),2) ((2 : Fin 8),2) (1,0) := by
  change KRKEightEdge.Region ((1 : Fin 8),2) ((2 : Fin 8),2) (1,0)
  refine ⟨Or.inl (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
    decide
  · intro i guard
    cases i with
    | west => exact Or.inl ⟨rfl,Or.inr (Or.inl ⟨.near,rfl,True.intro⟩)⟩
    | east =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (1,0)
          (KRKEightEdge.destination (1,0) .east) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northWest =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (1,0)
          (KRKEightEdge.destination (1,0) .northWest) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (1,0)
          (KRKEightEdge.destination (1,0) .north) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((1 : Fin 8),2) ((2 : Fin 8),2) (1,0)
          (KRKEightEdge.destination (1,0) .northEast) := by
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right]
        decide
      exact False.elim (absent guard)

private theorem corner_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((2 : Fin 8),2) (0,0) :=
  KRKNineGeometry.king_step_clear (ns := ((1 : Fin 8),2)) (by decide) (by decide) (by decide) corner_eight

private theorem near_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((2 : Fin 8),2) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((1 : Fin 8),2)) (by decide) (by decide) (by decide) near_eight

private theorem high_near_nine : KRKNineGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),2) (1,0) := by
  let q := krkPos .white (3,2) (2,2) (1,0) .white
  have material : IsKRK q .white (3,2) (2,2) (1,0) := ⟨by decide,by decide,by decide,rfl⟩
  have notCheck : ¬RookSees ((2 : Fin 8),2) (1,0) (3,2) (1,0) := by dsimp [RookSees,RookLine,OnSeg]; decide
  have sevenClear := (KRKSevenNear.clear_iff material.1 material.2.2.1 notCheck).mpr
    (Or.inr ⟨.high,rfl,Or.inr (Or.inl ⟨rfl,by decide⟩)⟩)
  have seven := KRKSevenGeometry.sufficient material rfl (by decide) notCheck sevenClear
  exact KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono seven (by decide))

private theorem west_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((2 : Fin 8),2) (0,1) := by
  let g := Frame.ofSym symSwap
  have back := KRKNineGeometry.frame_map g (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide) high_near_nine
  simpa only [g,Frame.ofSym,symSwap] using back

private theorem inner_nine : KRKNineGeometry.Clear ((2 : Fin 8),3) ((2 : Fin 8),2) (1,1) := by
  have region : KRKEightGlobal.Region ((1 : Fin 8),3) ((2 : Fin 8),2) (1,1) := by
    change KRKEightInteriorExact.Region ((1 : Fin 8),3) ((2 : Fin 8),2) (1,1)
    exact ⟨rfl,Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,by decide⟩⟩)⟩⟩⟩
  exact KRKNineGeometry.king_step_clear (ns := ((1 : Fin 8),3)) (by decide) (by decide) (by decide) region

private theorem high_inner_nine : KRKNineGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),2) (1,1) := by
  have region : KRKEightGlobal.Region ((3 : Fin 8),1) ((2 : Fin 8),2) (1,1) := by
    change KRKEightInteriorExact.Region ((3 : Fin 8),1) ((2 : Fin 8),2) (1,1)
    exact ⟨rfl,Or.inl ⟨rfl,Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,by decide⟩⟩)⟩⟩⟩
  exact KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),1)) (by decide) (by decide) (by decide) region

private theorem middle_nine : KRKNineGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),2) (3,0) := by
  let q := krkPos .white (3,2) (2,2) (3,0) .white
  have material : IsKRK q .white (3,2) (2,2) (3,0) := ⟨by decide,by decide,by decide,rfl⟩
  have notCheck : ¬RookSees ((2 : Fin 8),2) (3,0) (3,2) (3,0) := by dsimp [RookSees,RookLine,OnSeg]; decide
  have fiveClear := (KRKFiveMiddle.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) (by decide)
    material.1 material.2.2.1 notCheck).mpr (Or.inr (Or.inl rfl))
  have five := KRKFiveGeometry.sufficient material rfl (by decide) notCheck fiveClear
  exact KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono five (by decide))

private theorem corner_ten : KRKTenGlobal.Region ((2 : Fin 8),3) ((2 : Fin 8),2) (0,0) := by
  have clear : KRKTenGeometry.Clear ((2 : Fin 8),3) ((2 : Fin 8),2) (0,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),1),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    · intro t guard
      have targets : t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · exact west_nine
      · exact near_nine
      · exact inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem near_ten : KRKTenGlobal.Region ((2 : Fin 8),3) ((2 : Fin 8),2) (1,0) := by
  have clear : KRKTenGeometry.Clear ((2 : Fin 8),3) ((2 : Fin 8),2) (1,0) := by
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
      · exact corner_nine
      · exact west_nine
      · exact inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem second_ten : KRKTenGlobal.Region ((3 : Fin 8),2) ((2 : Fin 8),2) (2,0) := by
  have clear : KRKTenGeometry.Clear ((3 : Fin 8),2) ((2 : Fin 8),2) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · exact high_near_nine
      · exact middle_nine
      · exact high_inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem bottom_eleven {j : Fin 8} (choice : j = 0 ∨ j = 1 ∨ j = 2) :
    KRKElevenGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) (j,0) := by
  rcases choice with rfl | rfl | rfl
  · exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),3))
      (by decide) (by decide) (by decide) corner_ten
  · exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),3))
      (by decide) (by decide) (by decide) near_ten
  · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2))
      (by decide) (by decide) (by decide) second_ten

/-- The protected diagonal is newly winning at twelve plies. Every
inward weak reply is blocked; all five edge escapes have explicit entries. -/
theorem clear : KRKTwelveGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) (1,1) := by
  refine ⟨Or.inr (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
    decide
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
        t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have west : ∀ {j : Fin 8}, j = 1 ∨ j = 2 →
        KRKCornerWeakBand.Guard ((3 : Fin 8),3) ((2 : Fin 8),2) (1,1) (0,j) →
        KRKElevenGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) (0,j) := by
      intro j choice guard
      let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f ((3 : Fin 8),3)) (g.f ((2 : Fin 8),2)) (g.f ((0 : Fin 8),j)) :=
        bottom_eleven (Or.inr choice)
      have back := KRKElevenGeometry.frame_map g.inverse (by decide)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl | rfl | rfl
    · exact bottom_eleven (Or.inl rfl)
    · exact bottom_eleven (Or.inr (Or.inl rfl))
    · exact bottom_eleven (Or.inr (Or.inr rfl))
    · exact west (Or.inl rfl) guard
    · exact west (Or.inr rfl) guard

theorem kernel_twelve {q : Position} {σ : Colour}
    (material : IsKRK q σ (3,3) (2,2) (1,1)) (turn : q.turn = σ.opp) : MateWithin σ 12 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr clear

theorem kernel_exact_twelve {q : Position} {σ : Colour}
    (material : IsKRK q σ (3,3) (2,2) (1,1)) (turn : q.turn = σ.opp) :
    MateWithin σ 12 q ∧ ¬MateWithin σ 11 q := by
  refine ⟨kernel_twelve material turn,?_⟩
  intro eleven
  have ten := KRKTenGeometry.weak_eleven_ten material turn eleven
  have region := (KRKTenInner.kernel_ten_iff material turn (by decide)).mp ten
  dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
    KRKTenInner.SideExtra,KRKTenInner.HighExtra,symSwap] at region
  omega

end EndgameChess.Rules.KRKTwelveInnerDiagonal
