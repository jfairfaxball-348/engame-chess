import EndgameChess.Rules.KRKEightInterior

namespace EndgameChess.Rules.KRKEightStrip
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

private theorem val0 : ((0 : Fin 8).val) = 0 := rfl
private theorem val1 : ((1 : Fin 8).val) = 1 := rfl
private theorem val2 : ((2 : Fin 8).val) = 2 := rfl
private theorem val3 : ((3 : Fin 8).val) = 3 := rfl

/-- A genuinely new eight-ply first-interior-strip family. -/
def Region (sk rs wk : Square) : Prop :=
  wk.1.val = 1 ∧ wk.2.val = 2 ∧ sk.1.val = 3 ∧ sk.2.val = 1 ∧ rs.2.val = 3 ∧ 3 ≤ rs.1.val

theorem region_replies {sk rs wk t : Square} (region : Region sk rs wk)
    (step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩) : KRKSevenGeometry.Clear sk rs t := by
  obtain ⟨wx,wy,sx,sy,ry,rx⟩ := region
  have guard := KRKCornerWeakBand.step_guard step
  have choices : (t.1.val = 0 ∧ t.2.val = 1) ∨ (t.1.val = 0 ∧ t.2.val = 2) ∨
      (t.1.val = 1 ∧ t.2.val = 1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,wx,wy,sx,sy,ry] at guard
    omega
  rcases choices with ⟨tx,ty⟩ | ⟨tx,ty⟩ | ⟨tx,ty⟩
  · apply KRKSevenReach.king_step_clear (ns := ((2 : Fin 8),2))
    · simp only [dInf,absDiff,sx,sy,val2]; omega
    · simp only [ne_iff_coords,val2]; omega
    · simp only [dInf,absDiff,tx,ty,val2]; omega
    · simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,Frame.comp,
        symSwap,symId,symX,KRKSixGlobal.EdgeRegion,KRKSixNear.Region,KRKSixNear.Extra,
        KRKFourPlyNearCorner.NearFour,tx,ty,val0,val1,val2,val3]
    · refine ⟨((0 : Fin 8),0),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,tx,ty,ry,
        val0,val1,val2,val3]
      omega
    · apply Or.inl
      simp only [dInf,absDiff,tx,ty,ry]; omega
  · apply KRKSevenReach.king_step_clear (ns := ((2 : Fin 8),2))
    · simp only [dInf,absDiff,sx,sy,val2]; omega
    · simp only [ne_iff_coords,val2]; omega
    · simp only [dInf,absDiff,tx,ty,val2]; omega
    · simp only [KRKSixGlobal.Region,KRKEdgeDepth.depth,tx,ty]
      simp [normalize,bottomFrame,Frame.ofSym,Frame.comp,symSwap,symId,symX,KRKSixGlobal.EdgeRegion,
        KRKSixSecond.Region,tx,ty,ry,val0,val1,val2,val3]
      omega
    · refine ⟨((0 : Fin 8),1),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,tx,ty,ry,
        val0,val1,val2,val3]
      omega
    · apply Or.inl
      simp only [dInf,absDiff,tx,ty,ry]; omega
  · let nr : Square := (rs.1,2)
    apply KRKSevenReach.rook_step_clear (nr := nr)
    · simp only [nr,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,tx,ty,ry,val2]
      simp <;> omega
    · simp only [nr,ne_iff_coords,sy,val2]; omega
    · simp only [nr,ne_iff_coords,tx,ty,val2]; omega
    · simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,KRKSixInwardCorner.GlobalRegion,
        KRKSixInterior.InnerCorner,KRKSixInwardCorner.Region,KRKSixInwardCorner.innerSym,symId,nr,
        sx,sy,tx,ty,val0,val1,val2,val3]
      omega
    · refine ⟨((0 : Fin 8),0),?_⟩
      simp only [nr,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,tx,ty,
        val0,val1,val2,val3]
      omega
    · apply Or.inl
      simp only [nr,dInf,absDiff,tx,ty,val2]; omega

theorem region_clear {sk rs wk : Square} (region : Region sk rs wk) : KRKEightGeometry.Clear sk rs wk := by
  have safe : SafeRook sk rs wk := by
    apply Or.inl
    dsimp [Region] at region
    simp only [dInf,absDiff]
    omega
  have live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t := by
    obtain ⟨wx,wy,sx,sy,ry,rx⟩ := region
    refine ⟨((0 : Fin 8),1),?_⟩
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,wx,wy,sx,sy,ry,
      val0,val1,val2,val3]
    omega
  exact ⟨safe,live,fun t h => region_replies region (StepM.lone h.1 h.2.1 h.2.2.1 h.2.2.2)⟩

theorem kernel_exact_eight {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (region : Region sk rs wk) :
    MateWithin σ 8 q ∧ ¬MateWithin σ 7 q := by
  have far : 2 ≤ dInf sk wk := by dsimp [Region] at region; simp only [dInf,absDiff]; omega
  have inside : 0 < KRKEdgeDepth.depth wk := by dsimp [Region] at region; dsimp [KRKEdgeDepth.depth]; omega
  have notInner : ¬KRKSixInterior.InnerCorner wk := by dsimp [Region] at region; dsimp [KRKSixInterior.InnerCorner]; omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  refine ⟨(KRKEightGeometry.kernel_eight_iff material turn notMate).mpr (region_clear region),?_⟩
  intro seven
  exact notInner (KRKSixInterior.weak_six_interior_corner material turn far inside
    (KRKSixGeometry.weak_seven_six material turn seven))

end EndgameChess.Rules.KRKEightStrip
