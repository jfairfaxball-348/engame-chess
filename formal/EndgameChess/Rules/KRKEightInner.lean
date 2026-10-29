import EndgameChess.Rules.KRKEightNearStrip

namespace EndgameChess.Rules.KRKEightInner
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Evaluated inward-corner eight-ply regions, before coordinate transposition. -/
def Horizontal (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧
    ((sk.2.val = 0 ∧ rs.2.val = 2 ∧ 3 ≤ rs.1.val) ∨
     (sk.2.val = 1 ∧ ((rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨
       (rs.1.val = 1 ∧ 3 ≤ rs.2.val ∧ rs.2.val ≤ 4))) ∨
     (sk.2.val = 2 ∧ ((rs.1.val = 2 ∧ rs.2.val = 2) ∨
       (rs.1.val = 1 ∧ 3 ≤ rs.2.val))))

def Region (sk rs : Square) : Prop := Horizontal sk rs ∨ Horizontal (symSwap.f sk) (symSwap.f rs)

theorem prison {sk rs : Square} (far : 2 ≤ dInf sk (1,1))
    (clear : KRKEightGeometry.Clear sk rs (1,1)) : CornerPrison sk rs := by
  apply corner_prison rfl rfl far clear.1
  intro t distance inside
  have notInner : ¬KRKSixInterior.InnerCorner t := by
    dsimp [dInf,absDiff] at distance
    dsimp [KRKSixInterior.InnerCorner]
    omega
  exact (KRKEightInterior.covered_or_inner clear.1 distance inside
    (fun u step => clear.2.2 u (KRKCornerWeakBand.step_guard step))).resolve_right notInner

theorem row_two_necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3) (sy : sk.2.val ≤ 2)
    (ry : rs.2.val = 2) (clear : KRKEightGeometry.Clear sk rs (1,1)) :
    (sk.2.val = 0 ∧ 3 ≤ rs.1.val) ∨
    (sk.2.val = 1 ∧ 2 ≤ rs.1.val) ∨ (sk.2.val = 2 ∧ rs.1.val = 2) := by
  have safe := clear.1
  have rx : 2 ≤ rs.1.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,1) (1,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry]
    dsimp
    omega
  have low : sk.2.val = 0 → 3 ≤ rs.1.val := by
    intro zero
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have upper : sk.2.val = 2 → rs.1.val = 2 := by
    intro two
    by_cases different : rs.1.val = 2
    · exact different
    apply False.elim
    have notThree : rs.1.val ≠ 3 := by
      intro same
      exact apart (Prod.ext (Fin.ext (sx.trans same.symm)) (Fin.ext (two.trans ry.symm)))
    have insideGuard : KRKCornerWeakBand.Guard sk rs (1,1) (1,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry,two]
      simp <;> omega
    have domain := KRKSevenReach.weak_domain (clear.2.2 _ insideGuard)
    rcases domain with edge | inner
    · change 1 = 0 at edge; contradiction
    · dsimp [KRKSixInterior.InnerCorner] at inner; omega
  omega

private theorem second_high_necessary {sk rs : Square} (sx : sk.1.val = 1) (sy : sk.2.val = 3)
    (ry : rs.2.val = 1) (clear : KRKSevenGeometry.Clear sk rs (2,0)) :
    rs.1.val = 3 ∨ rs.1.val = 4 := by
  rcases clear with immediate | ⟨i,distance,_,_,region,_,_⟩ | ⟨i,_,a,v,sees,_,_,region,_,_⟩
  · simp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget,
      sx,sy,ry,dInf,absDiff] at immediate <;> omega
  · simp only [KRKSevenSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSevenSlots.point] at distance region
    simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSixGlobal.EdgeRegion,KRKSixSecond.Region,ry] at region
    simp only [dInf,absDiff,sx,sy] at distance
    dsimp at distance
    omega
  · simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSixGlobal.EdgeRegion,KRKSixSecond.Region,sy] at region

theorem file_one_necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (_sy : sk.2.val = 1 ∨ sk.2.val = 2) (rx : rs.1.val = 1)
    (clear : KRKEightGeometry.Clear sk rs (1,1)) :
    3 ≤ rs.2.val ∧ (sk.2.val = 1 → rs.2.val ≤ 4) := by
  have safe := clear.1
  have height : 3 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
  refine ⟨height,?_⟩
  intro one
  have guard : KRKCornerWeakBand.Guard sk rs (1,1) (0,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have child := KRKSevenReach.frame_map g apart
    (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm
    guard.2.2.1 guard.2.2.2 (clear.2.2 _ guard)
  have bound := second_high_necessary (sk := g.f sk) (rs := g.f rs) one sx rx child
  dsimp [g,Frame.ofSym,symSwap] at bound
  omega

theorem no_seven_diagonal :
    ¬KRKSevenGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) ((0 : Fin 8),0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,_,region,_,_⟩ | ⟨i,_,a,v,sees,_,_,region,_,_⟩
  · simp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate <;> omega
  · simp only [KRKSevenSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSevenSlots.point] at distance apart region
    simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSixGlobal.EdgeRegion,KRKSixCorner.Region] at region
    simp only [dInf,absDiff,ne_iff_coords] at distance apart
    dsimp at distance apart
    omega
  · cases a <;>
      simp [KRKSevenSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
        KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg] at sees <;>
      simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
        KRKSixGlobal.EdgeRegion,KRKSixCorner.Region,KRKSevenSlots.frame,
        KRKCornerSlotBarriers.Axis.target] at region <;> omega

theorem diagonal_not_clear :
    ¬KRKEightGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) ((1 : Fin 8),1) := by
  intro clear
  apply no_seven_diagonal (clear.2.2 (0,0) ?_)
  simp [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] <;> omega

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKEightGeometry.Clear sk rs (1,1)) : Region sk rs := by
  have horizontal : ∀ {sk rs : Square}, sk ≠ rs → sk.1.val = 3 → sk.2.val ≤ 2 →
      rs.2.val = 2 → KRKEightGeometry.Clear sk rs (1,1) → Horizontal sk rs := by
    intro sk rs distinct sx sy ry clear
    have choices := row_two_necessary distinct sx sy ry clear
    dsimp [Horizontal]
    omega
  have file : ∀ {sk rs : Square}, sk ≠ rs → sk.1.val = 3 → (sk.2.val = 1 ∨ sk.2.val = 2) →
      rs.1.val = 1 → KRKEightGeometry.Clear sk rs (1,1) → Horizontal sk rs := by
    intro sk rs distinct sx sy rx clear
    have bound := file_one_necessary distinct sx sy rx clear
    dsimp [Horizontal]
    omega
  have swapped := KRKCastleEight.frame_map (Frame.ofSym symSwap) apart clear
  rcases prison far clear with ⟨sx,sy,ry⟩ | ⟨sy,sx,rx⟩ | ⟨sx,sy,rx⟩ | ⟨sy,sx,ry⟩ | ⟨sx,sy,rx,ry⟩
  · exact Or.inl (horizontal apart sx sy ry clear)
  · exact Or.inr (horizontal (symSwap.ne_iff.mpr apart) sy sx rx swapped)
  · exact Or.inl (file apart sx sy rx clear)
  · exact Or.inr (file (symSwap.ne_iff.mpr apart) sy sx ry swapped)
  · have king : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rook : rs = ((2 : Fin 8),2) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    rw [king,rook] at clear
    exact False.elim (diagonal_not_clear clear)

private theorem horizontal_safe {sk rs : Square} (region : Horizontal sk rs) : SafeRook sk rs (1,1) := by
  dsimp [Horizontal,SafeRook,dInf,absDiff] at *
  omega

private theorem horizontal_distinct {sk rs : Square} (region : Horizontal sk rs) : sk ≠ rs := by
  dsimp [Horizontal] at region
  simp only [ne_iff_coords]
  omega

private theorem corner_reply {sk rs : Square} (region : Horizontal sk rs) :
    KRKSevenGeometry.Clear sk rs (0,0) := by
  have shape := region
  dsimp [Horizontal] at shape
  let ns : Square := if rs.2.val = 2 then (2,1) else (2,2)
  have distance : dInf sk ns = 1 := by
    dsimp [ns]; split <;> dsimp [dInf,absDiff] <;> omega
  have apart : ns ≠ rs := by
    simp only [ns,ne_iff_coords]; split <;> dsimp <;> omega
  have far : 2 ≤ dInf ns ((0 : Fin 8),0) := by dsimp [ns]; split <;> decide
  have destination : KRKSixGlobal.Region ns rs (0,0) := by
    simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSixGlobal.EdgeRegion,KRKSixCorner.Region,ns]
    split <;> simp_all <;> omega
  have live : KRKSevenGeometry.Live ns rs (0,0) := by
    refine ⟨((0 : Fin 8),1),?_⟩
    simp only [ns]; split <;>
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] <;>
      simp <;> omega
  have safe : SafeRook ns rs (0,0) := by
    apply Or.inl
    dsimp [dInf,absDiff]
    omega
  exact KRKSevenReach.king_step_clear distance apart far destination live safe

private theorem south_reply {sk rs : Square} (region : Horizontal sk rs)
    (guard : KRKCornerWeakBand.Guard sk rs (1,1) (1,0)) : KRKSevenGeometry.Clear sk rs (1,0) := by
  have shape := region
  dsimp [Horizontal] at shape
  have row : rs.2.val = 2 := by
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
    dsimp at guard
    omega
  apply (KRKSevenNear.clear_iff (horizontal_distinct region) guard.2.1.symm guard.2.2.2).mpr
  apply Or.inr
  rcases shape.2 with ⟨sy,_,rx⟩ | ⟨sy,_⟩ | ⟨sy,choice⟩
  · refine ⟨.low,Prod.ext (Fin.ext shape.1) (Fin.ext sy),?_⟩
    exact Or.inl rx
  · refine ⟨.side,Prod.ext (Fin.ext shape.1) (Fin.ext sy),?_⟩
    exact Or.inl (by omega)
  · refine ⟨.high,Prod.ext (Fin.ext shape.1) (Fin.ext sy),?_⟩
    exact Or.inr (Or.inl ⟨row,by omega⟩)

private theorem west_reply {sk rs : Square} (region : Horizontal sk rs)
    (guard : KRKCornerWeakBand.Guard sk rs (1,1) (0,1)) : KRKSevenGeometry.Clear sk rs (0,1) := by
  let g := Frame.ofSym symSwap
  have shape := region
  dsimp [Horizontal] at shape
  have seven : KRKSevenNear.Seven (g.f sk) (g.f rs) := by
    apply Or.inl
    rcases shape.2 with ⟨sy,ry,rx⟩ | ⟨sy,choice⟩ | ⟨sy,choice⟩
    · refine ⟨.west,?_,?_,?_,?_⟩
      · change rs.2.val = 2 ∧ 2 ≤ rs.1.val; omega
      · dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
      · simp only [g,Frame.ofSym,symSwap,KRKSevenNear.king,ne_iff_coords]; dsimp; omega
      · apply Or.inl; dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
    · rcases choice with ⟨ry,rx⟩ | ⟨rx,low,high⟩
      · refine ⟨.middle,?_,?_,?_,?_⟩
        · dsimp [KRKSevenNear.RookRegion,g,Frame.ofSym,symSwap]; omega
        · dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
        · simp only [g,Frame.ofSym,symSwap,KRKSevenNear.king,ne_iff_coords]; dsimp; omega
        · apply Or.inl; dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
      · refine ⟨.diagonal,True.intro,?_,?_,?_⟩
        · dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
        · simp only [g,Frame.ofSym,symSwap,KRKSevenNear.king,ne_iff_coords]; dsimp; omega
        · apply Or.inl; dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
    · rcases choice with ⟨rx,ry⟩ | ⟨rx,low⟩
      · refine ⟨.middle,?_,?_,?_,?_⟩
        · dsimp [KRKSevenNear.RookRegion,g,Frame.ofSym,symSwap]; omega
        · dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
        · simp only [g,Frame.ofSym,symSwap,KRKSevenNear.king,ne_iff_coords]; dsimp; omega
        · apply Or.inl; dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
      · refine ⟨.diagonal,True.intro,?_,?_,?_⟩
        · dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
        · simp only [g,Frame.ofSym,symSwap,KRKSevenNear.king,ne_iff_coords]; dsimp; omega
        · apply Or.inl; dsimp [g,Frame.ofSym,symSwap,KRKSevenNear.king,dInf,absDiff]; omega
  have mapped := (KRKSevenNear.clear_iff (g.ne_iff.mpr (horizontal_distinct region))
    (g.ne_iff.mpr guard.2.1.symm) (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mpr seven
  have back := KRKSevenReach.frame_map g.inverse (g.ne_iff.mpr (horizontal_distinct region))
    (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
    (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
  simpa only [Frame.inverse,g.left_inv] using back

private theorem east_reply {sk rs : Square} (region : Horizontal sk rs)
    (guard : KRKCornerWeakBand.Guard sk rs (1,1) (2,0)) : KRKSevenGeometry.Clear sk rs (2,0) := by
  have shape := region
  dsimp [Horizontal] at shape
  have position : sk.1.val = 3 ∧ sk.2.val = 2 ∧
      ((rs.1.val = 2 ∧ rs.2.val = 2) ∨ (rs.1.val = 1 ∧ 3 ≤ rs.2.val)) := by
    have far := guard.2.2.1
    dsimp [dInf,absDiff] at far
    omega
  obtain ⟨sx,sy,rook⟩ := position
  apply KRKSevenReach.rook_step_clear (nr := ((1 : Fin 8),2))
  · simp only [RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy]; simp <;> omega
  · simp only [ne_iff_coords,sx,sy]; dsimp; omega
  · decide
  · simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSixGlobal.EdgeRegion,KRKSixSecond.Region,sx,sy]
  · refine ⟨((3 : Fin 8),0),?_⟩
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy]
    simp <;> omega
  · apply Or.inl
    decide

private theorem upper_reply {sk rs : Square} (region : Horizontal sk rs)
    (guard : KRKCornerWeakBand.Guard sk rs (1,1) (0,2)) : KRKSevenGeometry.Clear sk rs (0,2) := by
  have shape := region
  dsimp [Horizontal] at shape
  have position : sk.1.val = 3 ∧ (sk.2.val = 1 ∨ sk.2.val = 2) ∧
      rs.1.val = 1 ∧ 3 ≤ rs.2.val ∧ (sk.2.val = 1 → rs.2.val ≤ 4) := by
    have notCheck := guard.2.2.2
    simp only [RookSees,RookLine,OnSeg] at notCheck
    dsimp at notCheck
    omega
  obtain ⟨sx,sy,rx,height,upper⟩ := position
  let g := Frame.ofSym symSwap
  let ns : Square := if rs.2.val ≤ 4 then (2,2) else (3,2)
  have distance : dInf (g.f sk) ns = 1 := by
    dsimp [ns]; split <;> dsimp [g,Frame.ofSym,symSwap,dInf,absDiff] <;> omega
  have apart : ns ≠ g.f rs := by
    simp only [ns]; split <;> simp only [g,Frame.ofSym,symSwap,ne_iff_coords] <;> dsimp <;> omega
  have far : 2 ≤ dInf ns ((2 : Fin 8),0) := by dsimp [ns]; split <;> decide
  have destination : KRKSixGlobal.Region ns (g.f rs) (2,0) := by
    simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,
      KRKSixGlobal.EdgeRegion,KRKSixSecond.Region,ns,g,symSwap]
    split <;> simp_all <;> omega
  have live : KRKSevenGeometry.Live ns (g.f rs) (2,0) := by
    refine ⟨((1 : Fin 8),0),?_⟩
    simp only [ns]; split <;>
      simp only [g,Frame.ofSym,symSwap,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] <;>
      simp <;> omega
  have safe : SafeRook ns (g.f rs) (2,0) := by
    simp only [ns]; split <;> dsimp [g,Frame.ofSym,symSwap,SafeRook,dInf,absDiff] <;> omega
  have mapped := KRKSevenReach.king_step_clear distance apart far destination live safe
  have back := KRKSevenReach.frame_map g.inverse (g.ne_iff.mpr (horizontal_distinct region))
    (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
    (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
  simpa only [Frame.inverse,g.left_inv] using back

theorem horizontal_replies {sk rs t : Square} (region : Horizontal sk rs)
    (guard : KRKCornerWeakBand.Guard sk rs (1,1) t) : KRKSevenGeometry.Clear sk rs t := by
  have choices : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨
      t = ((2 : Fin 8),0) ∨ t = ((0 : Fin 8),2) := by
    have shape := region
    dsimp [Horizontal] at shape
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
    simp only [square_eq_iff,Fin.ext_iff]
    dsimp at guard ⊢
    omega
  rcases choices with rfl | rfl | rfl | rfl | rfl
  · exact corner_reply region
  · exact south_reply region guard
  · exact west_reply region guard
  · exact east_reply region guard
  · exact upper_reply region guard

theorem horizontal_clear {sk rs : Square} (region : Horizontal sk rs) :
    KRKEightGeometry.Clear sk rs (1,1) := by
  refine ⟨horizontal_safe region,⟨((0 : Fin 8),0),?_⟩,fun _ guard => horizontal_replies region guard⟩
  have shape := region
  dsimp [Horizontal] at shape
  simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
  simp <;> omega

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKEightGeometry.Clear sk rs (1,1) := by
  rcases region with horizontal | vertical
  · exact horizontal_clear horizontal
  · have mapped := horizontal_clear vertical
    have back := KRKCastleEight.frame_map (Frame.ofSym symSwap) (horizontal_distinct vertical) mapped
    simpa only [Frame.ofSym,symSwap.invol,
      show symSwap.f ((1 : Fin 8),1) = ((1 : Fin 8),1) from rfl] using back

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1)) :
    KRKEightGeometry.Clear sk rs (1,1) ↔ Region sk rs := ⟨necessary apart far,sufficient⟩

theorem kernel_eight_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1)) :
    MateWithin σ 8 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKEightGeometry.kernel_eight_iff material turn notMate).trans (clear_iff material.1 far)

theorem kernel_exact_eight {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1)) :
    (MateWithin σ 8 q ∧ ¬MateWithin σ 7 q) ↔
      Region sk rs ∧ ¬KRKSixInwardCorner.Region sk rs := by
  constructor
  · rintro ⟨eight,notSeven⟩
    refine ⟨(kernel_eight_iff material turn far).mp eight,?_⟩
    intro sixRegion
    have six := (KRKSixInwardCorner.kernel_six_iff material turn far rfl rfl).mpr sixRegion
    exact notSeven (mateWithin_mono six (by decide))
  · rintro ⟨region,notSix⟩
    refine ⟨(kernel_eight_iff material turn far).mpr region,?_⟩
    intro seven
    exact notSix ((KRKSixInwardCorner.kernel_six_iff material turn far rfl rfl).mp
      (KRKSixGeometry.weak_seven_six material turn seven))

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),1))
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKEightGeometry.Clear sk rs wk ↔ Region (g.f sk) (g.f rs) := by
  have mappedFar : 2 ≤ dInf (g.f sk) (1,1) := by rw [←target,g.distance]; exact far
  constructor
  · intro clear
    have mapped := KRKCastleEight.frame_map g distinct clear
    rw [target] at mapped
    exact necessary (g.ne_iff.mpr distinct) mappedFar mapped
  · intro region
    have mapped := sufficient region
    rw [←target] at mapped
    have back := KRKCastleEight.frame_map g.inverse (g.ne_iff.mpr distinct) mapped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKEightInner
