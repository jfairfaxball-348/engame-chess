import EndgameChess.Rules.KRKTwelveInnerDiagonalExact
import EndgameChess.Rules.KRKTwelveInnerFileOne

namespace EndgameChess.Rules.KRKTwelveInnerOuter
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private theorem inner_nine : KRKNineGeometry.Clear (1,3) (3,2) (1,1) := by
  apply (KRKNineInner.clear_iff (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
  exact Or.inr (Or.inr ⟨.side,rfl,Or.inl ⟨by decide,by decide⟩⟩)

private theorem near_nine : KRKNineGeometry.Clear (1,3) (3,2) (1,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))

private theorem second_ten : KRKTenGlobal.Region (1,3) (3,2) (2,0) := by
  have clear : KRKTenGeometry.Clear (1,3) (3,2) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · exact near_nine
      · exact inner_nine
      · let g := Frame.ofSym symSwap
        have source : KRKNineGeometry.Clear (3,1) (2,3) (1,2) :=
          (KRKNineNearStrip.clear_iff (by decide) (by decide) (by decide) (by decide)
            (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
            (Or.inr ⟨rfl,Or.inl rfl⟩)
        have back := KRKNineGeometry.frame_map g (by decide) (by decide) (by decide) (by decide)
          (by dsimp [RookSees,RookLine,OnSeg]; decide) source
        simpa only [g,Frame.ofSym,symSwap] using back
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem high_inner_nine : KRKNineGeometry.Clear (3,2) (2,3) (1,1) :=
  (KRKNineInner.clear_iff (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr
    (Or.inr (Or.inl ⟨.high,rfl,Or.inl (by decide)⟩))

private theorem high_near_nine : KRKNineGeometry.Clear (3,2) (2,3) (1,0) := by
  let q := krkPos .white (3,2) (2,3) (1,0) .white
  have material : IsKRK q .white (3,2) (2,3) (1,0) := ⟨by decide,by decide,by decide,rfl⟩
  have notCheck : ¬RookSees ((2 : Fin 8),3) (1,0) (3,2) (1,0) := by dsimp [RookSees,RookLine,OnSeg]; decide
  have seven := KRKSevenGeometry.sufficient material rfl (by decide) notCheck
    ((KRKSevenNear.clear_iff material.1 material.2.2.1 notCheck).mpr
      (Or.inr ⟨.high,rfl,Or.inl (by decide)⟩))
  exact KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono seven (by decide))

private theorem corner_nine : KRKNineGeometry.Clear (1,3) (3,2) (0,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.corner_region (by decide))

private theorem west_nine : KRKNineGeometry.Clear (1,3) (3,2) (0,1) := by
  let q := krkPos .white (3,1) (2,3) (1,0) .white
  have material : IsKRK q .white (3,1) (2,3) (1,0) := ⟨by decide,by decide,by decide,rfl⟩
  have notCheck : ¬RookSees ((2 : Fin 8),3) (1,0) (3,1) (1,0) := by dsimp [RookSees,RookLine,OnSeg]; decide
  have seven := KRKSevenGeometry.sufficient material rfl (by decide) notCheck
    ((KRKSevenNear.clear_iff material.1 material.2.2.1 notCheck).mpr
      (Or.inr ⟨.side,rfl,Or.inl (by decide)⟩))
  have source := KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono seven (by decide))
  have back := KRKNineGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide) (by decide) (by decide) notCheck source
  simpa only [Frame.ofSym,symSwap] using back

private theorem second_nine : KRKNineGeometry.Clear (1,3) (3,2) (2,0) :=
  KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.second_region (Or.inr (Or.inl ⟨rfl,by decide⟩)))

private theorem east_nine : KRKNineGeometry.Clear (1,3) (3,2) (2,1) := by
  have source : KRKNineGeometry.Clear (3,1) (2,3) (1,2) :=
    (KRKNineNearStrip.clear_iff (by decide) (by decide) (by decide) (by decide)
      (by dsimp [RookSees,RookLine,OnSeg]; decide)).mpr (Or.inr ⟨rfl,Or.inl rfl⟩)
  have back := KRKNineGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide) source
  simpa only [Frame.ofSym,symSwap] using back

private theorem near_ten : KRKTenGlobal.Region (1,3) (3,2) (1,0) := by
  have clear : KRKTenGeometry.Clear (1,3) (3,2) (1,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((0 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨
          t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl | rfl | rfl
      · exact corner_nine
      · exact second_nine
      · exact west_nine
      · exact inner_nine
      · exact east_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem corner_ten_clear : KRKTenGeometry.Clear (1,3) (3,2) (0,0) := by
  refine ⟨Or.inl (by decide),⟨((0 : Fin 8),1),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
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

theorem high_second_ten : KRKTenGlobal.Region (3,2) (2,3) (2,0) := by
  have clear : KRKTenGeometry.Clear (3,2) (2,3) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · exact high_near_nine
      · let q := krkPos .white (3,2) (2,3) (3,0) .white
        have material : IsKRK q .white (3,2) (2,3) (3,0) := ⟨by decide,by decide,by decide,rfl⟩
        have notCheck : ¬RookSees ((2 : Fin 8),3) (3,0) (3,2) (3,0) := by dsimp [RookSees,RookLine,OnSeg]; decide
        have five := KRKFiveGeometry.sufficient material rfl (by decide) notCheck
          ((KRKFiveMiddle.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) (by decide)
            material.1 material.2.2.1 notCheck).mpr (Or.inr (Or.inl rfl)))
        exact KRKNineGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono five (by decide))
      · exact high_inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

theorem high_corner_ten : KRKTenGlobal.Region (3,2) (2,3) (0,0) := by
  have clear : KRKTenGeometry.Clear (3,2) (2,3) (0,0) := by
    refine ⟨Or.inl (by decide),⟨((0 : Fin 8),1),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    · intro t guard
      have targets : t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl | rfl
      · have source : KRKNineGeometry.Clear (2,3) (3,2) (1,0) :=
          KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
            (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))
        have back := KRKNineGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide) (by decide) (by decide)
          (by dsimp [RookSees,RookLine,OnSeg]; decide) source
        simpa only [Frame.ofSym,symSwap] using back
      · exact high_near_nine
      · exact high_inner_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem west_eleven {k j : Fin 8} (king : k = 1 ∨ k = 2) (edge : j = 0 ∨ j = 1 ∨ j = 2) :
    KRKElevenGeometry.Clear (4,k) (2,3) (0,j) := by
  let g := Frame.ofSym symSwap
  have source : KRKElevenGeometry.Clear (k,4) (3,2) (j,0) := by
    apply KRKElevenGeometry.king_step_clear (ns := ((1 : Fin 8),3))
    · rcases king with rfl | rfl <;> decide
    · decide
    · dsimp [dInf,absDiff]; omega
    · rcases edge with rfl | rfl | rfl
      · exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp corner_ten_clear
      · exact near_ten
      · exact second_ten
  have back := KRKElevenGeometry.frame_map g (by rcases king with rfl | rfl <;> decide)
    (by rcases king with rfl | rfl <;> simp) (by simp) (by dsimp [dInf,absDiff]; omega)
    (by rcases edge with rfl | rfl | rfl <;>
      simp [RookSees,RookLine,OnSeg,show ((3 : Fin 8).val) = 3 from rfl]) source
  simpa only [g,Frame.ofSym,symSwap] using back

theorem low_clear {k : Fin 8} (choice : k = 1 ∨ k = 2) : KRKTwelveGeometry.Clear (4,k) (2,3) (1,1) := by
  have low : 1 ≤ k.val ∧ k.val ≤ 2 := by rcases choice with rfl | rfl <;> decide
  refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
        t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases targets with rfl | rfl | rfl | rfl | rfl | rfl
    · have back := KRKTenGeometry.frame_map (Frame.ofSym symSwap) (by decide) corner_ten_clear
      have region : KRKTenGlobal.Region (3,1) (2,3) (0,0) :=
        (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp back
      exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1))
        (by dsimp [dInf,absDiff]; omega) (by decide) (by decide) region
    · exact KRKTwelveNearNewEntries.row_near_eleven choice
    · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2))
        (by dsimp [dInf,absDiff]; omega) (by decide) (by decide) high_second_ten
    · exact west_eleven choice (Or.inr (Or.inl rfl))
    · exact west_eleven choice (Or.inr (Or.inr rfl))
    · exact (KRKElevenNearStrip.clear_iff (by rcases choice with rfl | rfl <;> decide) (by decide)).mpr
        (Or.inl ⟨.side,by dsimp [KRKElevenNearStrip.king,dInf,absDiff]; omega,by decide,Or.inl ⟨rfl,by decide⟩⟩)

private theorem east_test {sk rs : Square} (apart : sk ≠ rs)
    (guard : KRKCornerWeakBand.Guard sk rs (2,0) (2,1))
    (clear : KRKNineGeometry.Clear sk rs (2,1)) : KRKNineNearStrip.Nine (symSwap.f sk) (symSwap.f rs) := by
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKNineGeometry.frame_map g apart
    notKing guard.2.1.symm
    guard.2.2.1 guard.2.2.2 clear
  exact (KRKNineNearStrip.clear_iff (g.ne_iff.mpr apart)
    (g.ne_iff.mpr notKing) (g.ne_iff.mpr guard.2.1.symm)
    (by change 2 ≤ dInf (g.f sk) (g.f ((2 : Fin 8),1)); rw [g.distance]; exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mp mapped

private theorem high_king_no_ten {sk : Square} (apart : sk ≠ ((3 : Fin 8),2))
    (sx : 2 ≤ sk.1.val) (sy : 3 ≤ sk.2.val) : ¬KRKTenGeometry.Clear sk (3,2) (2,0) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk ((3 : Fin 8),2) (2,0) (2,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  have evaluated := east_test apart guard (clear.2.2 _ guard)
  dsimp [KRKNineNearStrip.Nine,symSwap,dInf,absDiff] at evaluated
  simp only [square_eq_iff,Fin.ext_iff] at evaluated
  dsimp at evaluated
  omega

private theorem second_three_four_no_eleven : ¬KRKElevenGeometry.Clear ((3 : Fin 8),4) (3,2) (2,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((3 : Fin 8),4) (KRKElevenSlots.point i) = 1 at distance
    change KRKElevenSlots.point i ≠ ((3 : Fin 8),2) at apart
    change KRKTenEdge.Region (KRKElevenSlots.point i) (3,2) (2,0) at region
    have sx : 2 ≤ (KRKElevenSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have sy : 3 ≤ (KRKElevenSlots.point i).2.val := by dsimp [dInf,absDiff] at distance; omega
    exact high_king_no_ten apart sx sy
      ((KRKTenEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide) apart).mpr region)
  · let nr := a.target ((3 : Fin 8),2) v
    change RookSees ((3 : Fin 8),2) nr (3,4) (2,0) at sees
    change nr ≠ ((3 : Fin 8),4) at notKing
    change KRKTenEdge.Region ((3 : Fin 8),4) nr (2,0) at region
    have ten := (KRKTenEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide) notKing.symm).mpr region
    have cover := KRKFourPlyEscape.covered_box
      (KRKTenSecondCorner.bad_neighbour_covered notKing.symm ten (t := (3,1)) (by decide)
        (Or.inr (Or.inr ⟨Or.inl rfl,by decide,by decide⟩)))
    dsimp at cover
    have line := sees.1
    have file : nr.1.val = 3 := by dsimp [RookLine] at line; omega
    have rank : nr.2.val ≠ 1 := by
      have safe := ten.1
      dsimp [SafeRook,dInf,absDiff] at safe
      omega
    have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),4) nr (2,0) (2,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,file]
      dsimp; omega
    have evaluated := east_test notKing.symm guard (ten.2.2 _ guard)
    dsimp [KRKNineNearStrip.Nine,symSwap,dInf,absDiff] at evaluated
    simp only [square_eq_iff,Fin.ext_iff] at evaluated
    dsimp at evaluated
    omega

theorem high_no_clear : ¬KRKTwelveGeometry.Clear ((4 : Fin 8),3) (2,3) (1,1) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard ((4 : Fin 8),3) (2,3) (1,1) (0,2) := by
    dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
  have mapped := KRKElevenGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide)
    (by decide) (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide) (clear.2.2 _ guard)
  exact second_three_four_no_eleven mapped

theorem clear_iff {k : Fin 8} (bounds : 1 ≤ k.val ∧ k.val ≤ 3) :
    KRKTwelveGeometry.Clear (4,k) (2,3) (1,1) ↔ k = 1 ∨ k = 2 := by
  constructor
  · intro clear
    have notThree : k ≠ 3 := by intro equal; rw [equal] at clear; exact high_no_clear clear
    simp only [Fin.ext_iff] at notThree ⊢
    dsimp at notThree ⊢
    omega
  · exact low_clear

theorem kernel_exact_twelve {q : Position} {σ : Colour} {k : Fin 8}
    (material : IsKRK q σ (4,k) (2,3) (1,1)) (turn : q.turn = σ.opp)
    (bounds : 1 ≤ k.val ∧ k.val ≤ 3) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ k = 1 ∨ k = 2 := by
  have far : 2 ≤ dInf ((4 : Fin 8),k) (1,1) := by dsimp [dInf,absDiff]; omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  constructor
  · exact fun h => (clear_iff bounds).mp ((KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp h.1)
  · intro choice
    refine ⟨(KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr (low_clear choice),?_⟩
    intro eleven
    have old := (KRKTenInner.kernel_ten_iff material turn far).mp (KRKTenGeometry.weak_eleven_ten material turn eleven)
    dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
      KRKTenInner.SideExtra,KRKTenInner.HighExtra,symSwap] at old
    rcases choice with rfl | rfl <;> omega

end EndgameChess.Rules.KRKTwelveInnerOuter
