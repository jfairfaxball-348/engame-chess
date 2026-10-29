import EndgameChess.Rules.KRKTwelveInnerUpperBoundary

namespace EndgameChess.Rules.KRKTwelveInnerUpperFive
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private theorem low_seven : KRKSevenGeometry.Clear (4,0) (4,1) (1,0) :=
  (KRKSevenNear.clear_iff (by decide) (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
    (Or.inl ⟨.low,Or.inl ⟨rfl,by decide⟩,by decide,by decide,Or.inl (by decide)⟩)

private theorem high_corner_seven : KRKSevenGeometry.Clear (4,2) (4,1) (0,0) := by
  apply (KRKSevenCorner.clear_iff (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
  refine Or.inl (Or.inr ⟨.highMiddle,by decide,by decide,?_,?_,Or.inl (by decide)⟩)
  · simp [KRKSixCorner.Region,KRKSevenCorner.king,symSwap,show ((3 : Fin 8).val) = 3 from rfl,show ((4 : Fin 8).val) = 4 from rfl]
  · refine Or.inr (Or.inl ?_)
    dsimp [KRKCornerWeakBand.Guard,KRKSevenCorner.king,symSwap,RookSees,RookLine,OnSeg]
    decide

private theorem high_second_seven : KRKSevenGeometry.Clear (4,2) (4,1) (2,0) :=
  (KRKSevenSecond.clear_iff (by decide) (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
    (Or.inl ⟨.east,Or.inr ⟨rfl,by decide⟩,by decide⟩)

private theorem upper_corner_seven : KRKSevenGeometry.Clear (1,3) (2,4) (0,0) :=
  (KRKSevenCorner.clear_iff (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
    (Or.inr (Or.inl ⟨.highNear,rfl,Or.inr (by decide)⟩))

private theorem upper_near_seven : KRKSevenGeometry.Clear (1,3) (2,4) (1,0) :=
  (KRKSevenNear.clear_iff (by decide) (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
    (Or.inl ⟨.middle,Or.inl (by decide),by decide,by decide,Or.inl (by decide)⟩)

private theorem upper_west_seven : KRKSevenGeometry.Clear (1,3) (2,4) (0,1) := by
  have source : KRKSevenGeometry.Clear (3,1) (4,2) (1,0) :=
    (KRKSevenNear.clear_iff (by decide) (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
      (Or.inr ⟨.side,rfl,Or.inl (by decide)⟩)
  have mapped := KRKSevenReach.frame_map (Frame.ofSym symSwap) (by decide) (by decide) (by decide)
    (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide) source
  simpa only [Frame.ofSym,symSwap] using mapped

private theorem upper_inner_seven : KRKSevenGeometry.Clear (1,3) (2,4) (1,1) :=
  (KRKSevenInner.clear_iff (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
    (Or.inr (Or.inr (Or.inr ⟨rfl,Or.inl rfl⟩)))

private theorem outer_low_eight {j : Fin 8} (choice : j = 0 ∨ j = 2) : KRKEightGlobal.Region (4,0) (4,1) (j,0) := by
  have clear : KRKEightGeometry.Clear (4,0) (4,1) (j,0) := by
    refine ⟨?_,?_,?_⟩
    · rcases choice with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inl (by decide)
    · rcases choice with rfl | rfl
      · refine ⟨((1 : Fin 8),0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
        decide
      · refine ⟨((1 : Fin 8),0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
        decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) := by
        rcases choice with rfl | rfl <;>
          simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard <;>
          simp only [square_eq_iff,Fin.ext_iff] <;> dsimp at guard ⊢ <;> omega
      rw [targets]
      exact low_seven
  have edge : KRKEdgeDepth.depth (j,0) = 0 := by simp [KRKEdgeDepth.depth]
  simp only [KRKEightGlobal.Region,edge,↓reduceIte]
  exact (KRKEightGlobal.edge_clear_iff (by decide) edge).mp clear

private theorem outer_high_eight {j : Fin 8} (choice : j = 1 ∨ j = 3) : KRKEightGlobal.Region (4,2) (4,1) (j,0) := by
  have clear : KRKEightGeometry.Clear (4,2) (4,1) (j,0) := by
    refine ⟨?_,?_,?_⟩
    · rcases choice with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inr (by decide)
    · rcases choice with rfl | rfl
      · refine ⟨((0 : Fin 8),0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
        decide
      · refine ⟨((2 : Fin 8),0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
        decide
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((2 : Fin 8),0) := by
        rcases choice with rfl | rfl <;>
          simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard <;>
          simp only [square_eq_iff,Fin.ext_iff] <;> dsimp at guard ⊢ <;> omega
      rcases targets with rfl | rfl
      · exact high_corner_seven
      · exact high_second_seven
  have edge : KRKEdgeDepth.depth (j,0) = 0 := by simp [KRKEdgeDepth.depth]
  simp only [KRKEightGlobal.Region,edge,↓reduceIte]
  exact (KRKEightGlobal.edge_clear_iff (by decide) edge).mp clear

private theorem upper_eight {j : Fin 8} (choice : j = 0 ∨ j = 1) : KRKEightGlobal.Region (1,3) (2,4) (j,0) := by
  have clear : KRKEightGeometry.Clear (1,3) (2,4) (j,0) := by
    refine ⟨?_,?_,?_⟩
    · rcases choice with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inl (by decide)
    · rcases choice with rfl | rfl
      · refine ⟨((0 : Fin 8),1),?_⟩
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
        decide
      · refine ⟨((0 : Fin 8),1),?_⟩
        dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
        decide
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),1) := by
        rcases choice with rfl | rfl <;>
          simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard <;>
          simp only [square_eq_iff,Fin.ext_iff] <;> dsimp at guard ⊢ <;> omega
      rcases targets with rfl | rfl | rfl | rfl
      · exact upper_corner_seven
      · exact upper_near_seven
      · exact upper_west_seven
      · exact upper_inner_seven
  have edge : KRKEdgeDepth.depth (j,0) = 0 := by simp [KRKEdgeDepth.depth]
  simp only [KRKEightGlobal.Region,edge,↓reduceIte]
  exact (KRKEightGlobal.edge_clear_iff (by decide) edge).mp clear

private theorem outer_low_nine {j : Fin 8} (choice : j = 0 ∨ j = 2) : KRKNineGeometry.Clear (5,1) (4,1) (j,0) :=
  KRKNineGeometry.king_step_clear (ns := ((4 : Fin 8),0)) (by decide) (by decide)
    (by rcases choice with rfl | rfl <;> decide) (outer_low_eight choice)

private theorem outer_high_nine {j : Fin 8} (choice : j = 1 ∨ j = 3) : KRKNineGeometry.Clear (5,1) (4,1) (j,0) :=
  KRKNineGeometry.king_step_clear (ns := ((4 : Fin 8),2)) (by decide) (by decide)
    (by rcases choice with rfl | rfl <;> decide) (outer_high_eight choice)

private theorem upper_nine {j : Fin 8} (choice : j = 0 ∨ j = 1) : KRKNineGeometry.Clear (1,4) (2,4) (j,0) :=
  KRKNineGeometry.king_step_clear (ns := ((1 : Fin 8),3)) (by decide) (by decide)
    (by rcases choice with rfl | rfl <;> decide) (upper_eight choice)

private theorem upper_inner_nine : KRKNineGeometry.Clear (1,4) (2,4) (1,1) := by
  have region : KRKEightGlobal.Region (1,3) (2,4) (1,1) :=
    KRKNineInner.global_region_iff.mpr (Or.inr ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,by decide⟩⟩)⟩)
  exact KRKNineGeometry.king_step_clear (ns := ((1 : Fin 8),3)) (by decide) (by decide) (by decide) region

private theorem upper_west_nine : KRKNineGeometry.Clear (1,4) (2,4) (0,1) := by
  have source : KRKNineGeometry.Clear (4,1) (4,2) (1,0) :=
    KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),1)) (by decide) (by decide) (by decide)
      (KRKTwelveInnerUpperEntries.low_near_eight (by decide))
  have mapped := KRKNineGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide) (by decide)
    (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide) source
  simpa only [Frame.ofSym,symSwap] using mapped

private theorem outer_near_ten : KRKTenGlobal.Region (5,1) (4,1) (1,0) := by
  have clear : KRKTenGeometry.Clear (5,1) (4,1) (1,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((2 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl
      · exact outer_low_nine (Or.inl rfl)
      · exact outer_low_nine (Or.inr rfl)
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem outer_second_ten : KRKTenGlobal.Region (5,1) (4,1) (2,0) := by
  have clear : KRKTenGeometry.Clear (5,1) (4,1) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl
      · exact outer_high_nine (Or.inl rfl)
      · exact outer_high_nine (Or.inr rfl)
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem upper_corner_ten : KRKTenGlobal.Region (1,4) (2,4) (0,0) := by
  have clear : KRKTenGeometry.Clear (1,4) (2,4) (0,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),1),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl
      · exact upper_west_nine
      · exact upper_nine (Or.inr rfl)
      · exact upper_inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem upper_near_ten : KRKTenGlobal.Region (1,4) (2,4) (1,0) := by
  have clear : KRKTenGeometry.Clear (1,4) (2,4) (1,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl
      · exact upper_nine (Or.inl rfl)
      · exact upper_west_nine
      · exact upper_inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

theorem clear : KRKTwelveGeometry.Clear ((1 : Fin 8),5) (2,4) (1,1) := by
  refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨
        t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
    have west : ∀ {j : Fin 8}, j = 1 ∨ j = 2 → KRKElevenGeometry.Clear (1,5) (2,4) (0,j) := by
      intro j choice
      have source : KRKElevenGeometry.Clear (5,1) (4,2) (j,0) := by
        apply KRKElevenGeometry.rook_step_clear (nr := ((4 : Fin 8),1))
        · rcases choice with rfl | rfl <;> dsimp [RookSees,RookLine,OnSeg] <;> decide
        · decide
        · simp
        · rcases choice with rfl | rfl
          · exact outer_near_ten
          · exact outer_second_ten
      have mapped := KRKElevenGeometry.frame_map (Frame.ofSym symSwap) (by decide)
        (by rcases choice with rfl | rfl <;> decide) (by rcases choice with rfl | rfl <;> decide)
        (by rcases choice with rfl | rfl <;> decide)
        (by rcases choice with rfl | rfl <;> dsimp [RookSees,RookLine,OnSeg] <;> decide) source
      simpa only [Frame.ofSym,symSwap] using mapped
    rcases targets with rfl | rfl | rfl | rfl | rfl
    · exact KRKElevenGeometry.king_step_clear (ns := ((1 : Fin 8),4)) (by decide) (by decide) (by decide) upper_corner_ten
    · exact KRKElevenGeometry.king_step_clear (ns := ((1 : Fin 8),4)) (by decide) (by decide) (by decide) upper_near_ten
    · exact west (Or.inl rfl)
    · exact west (Or.inr rfl)
    · exact (KRKElevenNearStrip.clear_iff (by decide) (by decide)).mpr
        (Or.inl ⟨.upperOne,by decide,by decide,⟨rfl,by decide⟩⟩)

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val ≤ 2)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) :
    KRKTwelveGeometry.Clear sk rs (1,1) ↔ sk = ((1 : Fin 8),5) ∧ rs = ((2 : Fin 8),4) := by
  constructor
  · exact KRKTwelveInnerUpperBoundary.five_necessary apart sx sy rx
  · rintro ⟨rfl,rfl⟩
    exact clear

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp)
    (sx : sk.1.val ≤ 2) (sy : sk.2.val = 5) (rx : rs.1.val = 2) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ sk = ((1 : Fin 8),5) ∧ rs = ((2 : Fin 8),4) := by
  have far : 2 ≤ dInf sk (1,1) := by dsimp [dInf,absDiff]; omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  constructor
  · exact fun h => (clear_iff material.1 sx sy rx).mp ((KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp h.1)
  · intro region
    refine ⟨(KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr ((clear_iff material.1 sx sy rx).mpr region),?_⟩
    intro eleven
    have old := (KRKTenInner.kernel_ten_iff material turn far).mp (KRKTenGeometry.weak_eleven_ten material turn eleven)
    dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
      KRKTenInner.SideExtra,KRKTenInner.HighExtra,symSwap] at old
    omega

end EndgameChess.Rules.KRKTwelveInnerUpperFive
