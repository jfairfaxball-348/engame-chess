import EndgameChess.Rules.KRKThirteenCentralStrip

namespace EndgameChess.Rules.KRKFourteenCentralEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem centered_twelve {r j : Fin 8} (height : 3 ≤ r.val) (choice : j = 3 ∨ j = 4) :
    KRKTwelveGlobal.Region (j,2) (2,r) (j,0) := by
  have apart : ((j,2) : Square) ≠ (2,r) := by simp only [ne_iff_coords]; dsimp; omega
  have notWeak : ((2,r) : Square) ≠ (j,0) := by simp only [ne_iff_coords]; dsimp; omega
  have far : 2 ≤ dInf (j,(2 : Fin 8)) (j,0) := by dsimp [dInf,absDiff]; omega
  have safe : SafeRook (j,2) (2,r) (j,0) := Or.inl (by dsimp [dInf,absDiff]; omega)
  have live : ∃ t, KRKCornerWeakBand.Guard (j,2) (2,r) (j,0) t := by
    rcases choice with rfl | rfl
    · refine ⟨((4 : Fin 8),0),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp; omega
    · refine ⟨((5 : Fin 8),0),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp; omega
  have region : KRKSixGlobal.Region (j,2) (2,r) (j,0) := by
    rcases choice with rfl | rfl <;>
      simpa [KRKSixGlobal.Region,KRKSixGlobal.EdgeRegion,KRKSixMiddle.Region,KRKEdgeDepth.depth,normalize,bottomFrame,
        Frame.ofSym,Frame.comp,symId,symX,show ((3 : Fin 8).val) = 3 from rfl,show ((4 : Fin 8).val) = 4 from rfl] using height
  let q := krkPos .white (j,2) (2,r) (j,0) .black
  have material : IsKRK q .white (j,2) (2,r) (j,0) := ⟨apart,ne_of_dInf_pos (by omega),notWeak,rfl⟩
  have six := (KRKSixGlobal.kernel_six_iff material rfl far).mpr (Or.inr ⟨region,safe,live⟩)
  have twelve := (KRKTwelveGlobal.kernel_twelve_iff material rfl far).mp (mateWithin_mono six (by decide))
  rcases twelve with terminal | region
  · have mate := (KRKMateGeometry.kernel_mate_iff material rfl far).mpr terminal
    obtain ⟨t,guard⟩ := live
    exact False.elim (mate.2 ⟨_,⟨_,KRKCornerWeakBand.guard_legal material rfl guard,rfl⟩⟩)
  · exact region

private theorem edge_thirteen {r j : Fin 8} (width : 3 ≤ r.val) (choice : j = 3 ∨ j = 4) :
    KRKThirteenGeometry.Clear (3,4) (r,2) (0,j) := by
  have source : KRKThirteenGeometry.Clear (4,3) (2,r) (j,0) :=
    KRKThirteenGeometry.king_step_clear (ns := (j,(2 : Fin 8)))
      (by rcases choice with rfl | rfl <;> decide)
      (by simp only [ne_iff_coords]; dsimp; omega) (by dsimp [dInf,absDiff]; omega) (centered_twelve width choice)
  have mapped := KRKThirteenGeometry.frame_map (Frame.ofSym symSwap)
    (by simp only [ne_iff_coords]; dsimp; omega)
    (by rcases choice with rfl | rfl <;> decide)
    (by simp only [ne_iff_coords]; dsimp; omega)
    (by dsimp [dInf,absDiff]; omega)
    (by simp only [RookSees,RookLine,OnSeg]; dsimp; rcases choice with rfl | rfl <;> omega) source
  simpa only [Frame.ofSym,symSwap] using mapped

private theorem upper_thirteen {r : Fin 8} (width : 3 ≤ r.val) : KRKThirteenGeometry.Clear (3,4) (r,2) (1,4) := by
  have source : KRKThirteenGeometry.Clear (3,3) (r,5) (1,3) :=
    (KRKThirteenCentralStrip.clear_iff (by simp) (by simp)).mpr
      (Or.inr ⟨.opposition,rfl,Or.inr (Or.inr (by change 5 ≤ 5; decide))⟩)
  have mapped := KRKThirteenGeometry.frame_map (Frame.ofSym symY) (by simp) (by decide) (by simp) (by decide)
    (by simp only [RookSees,RookLine,OnSeg]; dsimp; omega) source
  simpa [Frame.ofSym,symY,show ((3 : Fin 8).val) = 3 from rfl,show ((5 : Fin 8).val) = 5 from rfl] using mapped

/-- Central-strip opposition: the rook cuts the lower rank and every legal
escape admits an entry into a proved twelve-ply region. -/
theorem opposition_clear {r : Fin 8} (width : 3 ≤ r.val) : KRKFourteenGeometry.Clear (3,4) (r,2) (1,3) := by
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),3),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro t guard
    have targets : t = ((0 : Fin 8),3) ∨ t = ((0 : Fin 8),4) ∨ t = ((1 : Fin 8),4) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases targets with rfl | rfl | rfl
    · exact edge_thirteen width (Or.inl rfl)
    · exact edge_thirteen width (Or.inr rfl)
    · exact upper_thirteen width

theorem kernel_exact_fourteen {q : Position} {σ : Colour} {r : Fin 8}
    (material : IsKRK q σ (3,4) (r,2) (1,3)) (turn : q.turn = σ.opp) (width : 3 ≤ r.val) :
    MateWithin σ 14 q ∧ ¬MateWithin σ 13 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  refine ⟨(KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).mpr (opposition_clear width),?_⟩
  intro thirteen
  have twelve := KRKTwelveGeometry.weak_thirteen_twelve material turn thirteen
  have region := ((KRKTwelveGlobal.kernel_twelve_iff material turn (by decide)).mp twelve).resolve_left
    (fun t => notMate ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mpr t))
  have shape := KRKThirteenInteriorBarriers.central_region_iff.mp region
  dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,
    KRKTwelveCentralExact.Opposition] at shape
  simp only [square_eq_iff,Fin.ext_iff] at shape
  dsimp at shape
  omega

end EndgameChess.Rules.KRKFourteenCentralEntries
