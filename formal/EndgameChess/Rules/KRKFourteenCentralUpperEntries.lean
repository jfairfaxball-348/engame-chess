import EndgameChess.Rules.KRKFourteenCentralPrison

namespace EndgameChess.Rules.KRKFourteenCentralUpperEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem eight_second {r : Fin 8} (width : 4 ≤ r.val) : KRKEightGlobal.Region (3,2) (r,2) (2,0) := by
  change KRKEightEdge.Region (3,2) (r,2) (2,0)
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨.west,?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,KRKEightEdge.destination,KRKEightEdge.left,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro i guard
    cases i with
    | west =>
      refine Or.inr (Or.inl ⟨rfl,Or.inl ⟨.diagonal,True.intro,by decide,?_,?_⟩⟩)
      · simp only [KRKSevenNear.king,ne_iff_coords]; (try dsimp); omega
      · exact Or.inl (by dsimp [KRKSevenNear.king,dInf,absDiff]; omega)
    | east => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl,Or.inr (Or.inl rfl)⟩)))
    | northWest =>
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact ⟨rfl,Or.inl ⟨rfl,by change 3 ≤ r.val; omega,by decide⟩⟩
    | north =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) (r,2) (2,0) (2,1) := by
        intro h; have far := h.2.2.1; change 2 ≤ dInf ((3 : Fin 8),2) (2,1) at far; contradiction
      exact False.elim (absent guard)
    | northEast =>
      have absent : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) (r,2) (2,0) (3,1) := by
        intro h; have far := h.2.2.1; change 2 ≤ dInf ((3 : Fin 8),2) (3,1) at far; contradiction
      exact False.elim (absent guard)

private theorem eight_middle {r : Fin 8} (width : 4 ≤ r.val) : KRKEightGlobal.Region (3,2) (r,2) (3,0) := by
  change KRKEightEdge.Region (3,2) (r,2) (3,0)
  have five : KRKFiveMiddle.Five (symX.f (3,2)) (symX.f (r,2)) (3,0) := by
    refine Or.inr (Or.inr (Or.inr ⟨rfl,Or.inr (Or.inr ⟨rfl,?_⟩)⟩))
    change 7-r.val ≤ 3
    omega
  have bottom : KRKFiveMiddle.BottomFive (3,2) (r,2) (4,0) := by
    simpa [KRKFiveMiddle.BottomFive,symX,show ((3 : Fin 8).val) = 3 from rfl,show ((4 : Fin 8).val) = 4 from rfl] using five
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨.west,?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,KRKEightEdge.destination,KRKEightEdge.left,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro i guard
    cases i with
    | west => exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inr ⟨.east,rfl,True.intro⟩⟩))
    | east => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl,bottom⟩)))
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

private theorem ten_second {r : Fin 8} (width : 4 ≤ r.val) : KRKTenGlobal.Region (3,2) (r,2) (2,0) :=
  KRKTwelveNearFileEntries.eight_region_subset
    (by simp only [ne_iff_coords]; (try dsimp); omega) (by simp) (by decide) (eight_second width)

private theorem ten_middle {r : Fin 8} (width : 4 ≤ r.val) : KRKTenGlobal.Region (3,2) (r,2) (3,0) :=
  KRKTwelveNearFileEntries.eight_region_subset
    (by simp only [ne_iff_coords]; (try dsimp); omega) (by simp) (by decide) (eight_middle width)

private theorem eleven_inner {r : Fin 8} (width : 4 ≤ r.val) : KRKElevenGeometry.Clear (4,2) (r,2) (1,1) := by
  have region : KRKTenInner.Region (3,1) (r,2) :=
    Or.inl (Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,by change 2 ≤ r.val; omega⟩⟩)⟩)
  exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1)) (by decide) (by simp) (by decide)
    (KRKElevenInner.global_region_iff.mpr region)

private theorem eleven_near_transposed {r : Fin 8} (width : 5 ≤ r.val) : KRKElevenGeometry.Clear (4,2) (r,2) (2,1) := by
  have apart : ((2,4) : Square) ≠ (2,r) := by
    simp [ne_iff_coords,show ((4 : Fin 8).val) = 4 from rfl]; omega
  have source : KRKElevenGeometry.Clear (2,4) (2,r) (1,2) :=
    (KRKElevenNearStrip.clear_iff apart (by simp)).mpr
      (Or.inl ⟨.upperOne,by decide,by simp [KRKElevenNearStrip.king],⟨rfl,by change 3 ≤ r.val; omega⟩⟩)
  have mapped := KRKElevenGeometry.frame_map (Frame.ofSym symSwap)
    apart (by decide) (by simp) (by decide)
    (by simp only [RookSees,RookLine,OnSeg]; (try dsimp); omega) source
  simpa only [Frame.ofSym,symSwap] using mapped

private theorem eleven_centered {r : Fin 8} (width : 5 ≤ r.val) : KRKElevenGeometry.Clear (4,2) (r,2) (4,0) := by
  let q := krkPos .white (4,2) (r,2) (4,0) .white
  have apart : ((4,2) : Square) ≠ (r,2) := by simp only [ne_iff_coords]; (try dsimp); omega
  have notWeak : ((r,2) : Square) ≠ (4,0) := by simp
  have material : IsKRK q .white (4,2) (r,2) (4,0) := ⟨apart,by decide,notWeak,rfl⟩
  have notCheck : ¬RookSees (r,2) (4,0) (4,2) (4,0) := by
    simp only [RookSees,RookLine,OnSeg]; (try dsimp); omega
  have bottom : KRKFiveMiddle.BottomFive (4,2) (r,2) (4,0) := by
    change KRKFiveMiddle.Five (3,2) (symX.f (r,2)) (3,0)
    exact Or.inr (Or.inl rfl)
  have five := KRKFiveGeometry.sufficient material rfl (by decide) notCheck
    ((KRKFiveMiddle.bottom_clear_iff (wk := ((4 : Fin 8),0)) rfl (by decide) (by decide)
      apart (by decide) notWeak (by decide) notCheck).mpr bottom)
  exact KRKElevenGeometry.necessary material rfl (by decide) notCheck (mateWithin_mono five (by decide))

private theorem second_twelve {r : Fin 8} (width : 5 ≤ r.val) : KRKTwelveGlobal.Region (4,2) (r,2) (2,0) := by
  have clear : KRKTwelveGeometry.Clear (4,2) (r,2) (2,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; (try dsimp); omega
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) ∨ t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl | rfl
      · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1)) (by decide) (by simp) (by decide)
          (KRKTwelveInnerUpperEntries.low_near_ten (by omega))
      · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide)
          (by simp only [ne_iff_coords]; (try dsimp); omega) (by decide) (ten_middle (by omega))
      · exact eleven_inner (by omega)
      · exact eleven_near_transposed width
  exact (KRKTwelveGlobal.edge_clear_iff (by simp only [ne_iff_coords]; (try dsimp); omega) (by decide)).mp clear

private theorem middle_twelve {r : Fin 8} (width : 5 ≤ r.val) : KRKTwelveGlobal.Region (4,2) (r,2) (3,0) := by
  have clear : KRKTwelveGeometry.Clear (4,2) (r,2) (3,0) := by
    refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((2 : Fin 8),0),?_⟩,?_⟩
    · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; (try dsimp); omega
    · intro t guard
      have targets : t = ((2 : Fin 8),0) ∨ t = ((4 : Fin 8),0) ∨ t = ((2 : Fin 8),1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
      rcases targets with rfl | rfl | rfl
      · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide)
          (by simp only [ne_iff_coords]; (try dsimp); omega) (by decide) (ten_second (by omega))
      · exact eleven_centered width
      · exact eleven_near_transposed width
  exact (KRKTwelveGlobal.edge_clear_iff (by simp only [ne_iff_coords]; (try dsimp); omega) (by decide)).mp clear

private theorem upper_edge_thirteen {r j : Fin 8} (height : 5 ≤ r.val) (choice : j = 2 ∨ j = 3) :
    KRKThirteenGeometry.Clear (1,5) (2,r) (0,j) := by
  have source : KRKThirteenGeometry.Clear (5,1) (r,2) (j,0) := by
    apply KRKThirteenGeometry.king_step_clear (ns := ((4 : Fin 8),2)) (by decide)
    · simp only [ne_iff_coords]; (try dsimp); omega
    · rcases choice with rfl | rfl <;> decide
    · rcases choice with rfl | rfl
      · exact second_twelve height
      · exact middle_twelve height
  have mapped := KRKThirteenGeometry.frame_map (Frame.ofSym symSwap) (by simp)
    (by simp) (by simp) (by rcases choice with rfl | rfl <;> decide)
    (by simp only [RookSees,RookLine,OnSeg]; dsimp; rcases choice with rfl | rfl <;> omega) source
  simpa only [Frame.ofSym,symSwap] using mapped

theorem upper_one_clear {r : Fin 8} (height : 5 ≤ r.val) : KRKFourteenGeometry.Clear (1,5) (2,r) (1,3) := by
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),2),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]; (try dsimp); omega
  · intro t guard
    have targets : t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]; dsimp at guard ⊢; omega
    rcases targets with rfl | rfl | rfl
    · exact upper_edge_thirteen height (Or.inl rfl)
    · exact upper_edge_thirteen height (Or.inr rfl)
    · have region : KRKTwelveNearExact.Region (1,4) (2,r) :=
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,Or.inr (Or.inl ⟨rfl,by change 3 ≤ r.val; omega⟩)⟩)))
      exact KRKThirteenGeometry.king_step_clear (ns := ((1 : Fin 8),4)) (by decide) (by simp) (by decide)
        (KRKThirteenInteriorBarriers.near_region_iff.mpr region)

theorem kernel_upper_one_exact_fourteen {q : Position} {σ : Colour} {r : Fin 8}
    (material : IsKRK q σ (1,5) (2,r) (1,3)) (turn : q.turn = σ.opp) (height : 5 ≤ r.val) :
    MateWithin σ 14 q ∧ ¬MateWithin σ 13 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  refine ⟨(KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).mpr (upper_one_clear height),?_⟩
  intro thirteen
  have twelve := KRKTwelveGeometry.weak_thirteen_twelve material turn thirteen
  have region := ((KRKTwelveGlobal.kernel_twelve_iff material turn (by decide)).mp twelve).resolve_left
    (fun t => notMate ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mpr t))
  have shape := KRKThirteenInteriorBarriers.central_region_iff.mp region
  dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,
    KRKTwelveCentralExact.Opposition] at shape
  simp only [square_eq_iff,Fin.ext_iff] at shape
  (try dsimp at shape)
  simp only [show ((4 : Fin 8).val) = 4 from rfl] at shape
  omega

end EndgameChess.Rules.KRKFourteenCentralUpperEntries
