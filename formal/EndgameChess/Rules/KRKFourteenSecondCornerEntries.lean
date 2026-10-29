import EndgameChess.Rules.KRKFourteenSecondCorner

namespace EndgameChess.Rules.KRKFourteenSecondCornerEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem inner_region_iff {sk rs : Square} :
    KRKTwelveGlobal.Region sk rs (1,1) ↔ KRKTwelveInnerExact.Region sk rs := by
  simp [KRKTwelveGlobal.Region,KRKEdgeDepth.depth,KRKTwelveInteriorExact.Region,KRKTwelveInteriorExact.StripRegion,
    KRKEightInteriorExact.stripFrame,Frame.ofSym,symId]

private theorem inner_thirteen {r : Fin 8} (width : 3 ≤ r.val) : KRKThirteenGeometry.Clear (4,2) (r,3) (1,1) := by
  have region : KRKTwelveInnerExact.Region (3,2) (r,3) :=
    Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,Or.inl ⟨by change 2 ≤ r.val; omega,by change 2 ≤ 3; decide⟩⟩)))
  exact KRKThirteenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by simp) (by decide)
    (inner_region_iff.mpr region)

private theorem near_thirteen {r : Fin 8} (width : 3 ≤ r.val) : KRKThirteenGeometry.Clear (4,2) (r,3) (1,2) := by
  have region : KRKTwelveNearExact.Region (3,2) (r,3) :=
    Or.inr (Or.inl ⟨rfl,rfl,rfl,by change 2 ≤ r.val; omega⟩)
  exact KRKThirteenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by simp) (by decide)
    (KRKThirteenInteriorBarriers.near_region_iff.mpr region)

private theorem lower_thirteen {r : Fin 8} (width : 3 ≤ r.val) : KRKThirteenGeometry.Clear (4,2) (r,3) (2,1) := by
  have region : KRKTwelveNearExact.Region (2,4) (3,2) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,Or.inr rfl,rfl,rfl⟩)))
  have source : KRKThirteenGeometry.Clear (2,4) (3,r) (1,2) :=
    KRKThirteenGeometry.rook_step_clear (nr := ((3 : Fin 8),2))
      (by simp [RookSees,RookLine,OnSeg,show ((3 : Fin 8).val) = 3 from rfl]; omega)
      (by decide) (by decide) (KRKThirteenInteriorBarriers.near_region_iff.mpr region)
  have mapped := KRKThirteenGeometry.frame_map (Frame.ofSym symSwap)
    (by simp only [ne_iff_coords]; dsimp; omega) (by decide)
    (by simp only [ne_iff_coords]; dsimp; omega) (by decide)
    (by simp only [RookSees,RookLine,OnSeg]; dsimp; omega) source
  simpa only [Frame.ofSym,symSwap] using mapped

/-- The new second-corner opposition family, with a protected boundary rook. -/
theorem opposition_clear {r : Fin 8} (width : 3 ≤ r.val) : KRKFourteenGeometry.Clear (4,2) (r,3) (2,2) := by
  have safe : SafeRook ((4 : Fin 8),2) (r,3) (2,2) := by
    dsimp [SafeRook,dInf,absDiff]
    omega
  refine ⟨safe,⟨((1 : Fin 8),1),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro t guard
    have targets : t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases targets with rfl | rfl | rfl
    · exact inner_thirteen width
    · exact lower_thirteen width
    · exact near_thirteen width

theorem kernel_exact_fourteen {q : Position} {σ : Colour} {r : Fin 8}
    (material : IsKRK q σ (4,2) (r,3) (2,2)) (turn : q.turn = σ.opp) (width : 3 ≤ r.val) :
    MateWithin σ 14 q ∧ ¬MateWithin σ 13 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 2 = 0 at zero
    contradiction
  refine ⟨(KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).mpr (opposition_clear width),?_⟩
  intro thirteen
  have twelve := KRKTwelveGeometry.weak_thirteen_twelve material turn thirteen
  have region := ((KRKTwelveGlobal.kernel_twelve_iff material turn (by decide)).mp twelve).resolve_left
    (fun terminal => notMate ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mpr terminal))
  have shape := KRKThirteenInteriorBarriers.second_region_iff.mp region
  dsimp [KRKTwelveSecondCorner.Region,KRKTwelveSecondCorner.Horizontal,symSwap] at shape
  omega

end EndgameChess.Rules.KRKFourteenSecondCornerEntries
