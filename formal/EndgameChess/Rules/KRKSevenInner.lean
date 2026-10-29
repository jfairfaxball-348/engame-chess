import EndgameChess.Rules.KRKSevenNear

namespace EndgameChess.Rules.KRKSevenInner
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

private theorem inner_region {sk rs : Square} (region : KRKSixGlobal.Region sk rs (1,1)) :
    KRKSixInwardCorner.Region sk rs := by
  simpa [KRKSixGlobal.Region,KRKEdgeDepth.depth,KRKSixInwardCorner.GlobalRegion,
    KRKSixInterior.InnerCorner,KRKSixInwardCorner.innerSym,symId] using region

theorem inner_entry_necessary {sk rs : Square} (clear : KRKSevenGeometry.Clear sk rs (1,1)) :
    (rs.2.val = 2 ∧ 3 ≤ rs.1.val ∧ dInf sk (3,1) = 1) ∨
    (rs.1.val = 2 ∧ 3 ≤ rs.2.val ∧ dInf sk (1,3) = 1) ∨
    (sk.1.val = 3 ∧ sk.2.val = 1) ∨ (sk.1.val = 1 ∧ sk.2.val = 3) := by
  rcases clear with immediate | ⟨i,distance,_,_,region,_⟩ | ⟨i,_,a,v,_,_,_,region,_⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · have actual : dInf sk ((KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i)) = 1 := by
      have preserved := (KRKSevenSlots.frame ((1 : Fin 8),1)).distance sk
        ((KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i))
      rw [(KRKSevenSlots.frame ((1 : Fin 8),1)).right_inv,distance] at preserved
      exact preserved.symm
    rcases inner_region region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩
    · have equal : (KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i) = ((3 : Fin 8),1) :=
        Prod.ext (Fin.ext sx) (Fin.ext sy)
      exact Or.inl ⟨ry,rx,by rwa [equal] at actual⟩
    · have equal : (KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i) = ((1 : Fin 8),3) :=
        Prod.ext (Fin.ext sx) (Fin.ext sy)
      exact Or.inr (Or.inl ⟨rx,ry,by rwa [equal] at actual⟩)
  · rcases inner_region region with ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩
    · exact Or.inr (Or.inr (Or.inl ⟨sx,sy⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨sx,sy⟩))

def HorizontalRook (rs : Square) : Prop :=
  rs.2.val = 2 ∨ 4 ≤ rs.1.val ∨ (rs.1.val = 3 ∧ 3 ≤ rs.2.val)

theorem horizontal_line_necessary {rs nr : Square} (apart : ((3 : Fin 8),1) ≠ rs)
    (sees : RookSees rs nr (3,1) (1,1)) (row : nr.2.val = 2) (width : 3 ≤ nr.1.val) :
    HorizontalRook rs := by
  simp only [RookSees,RookLine,OnSeg,ne_iff_coords,row] at sees
  simp only [ne_iff_coords] at apart
  dsimp [HorizontalRook] at *
  try dsimp at sees apart
  omega

theorem horizontal_line_sufficient {rs : Square} (condition : HorizontalRook rs) :
    ∃ nr, RookSees rs nr (3,1) (1,1) ∧ nr.2.val = 2 ∧ 3 ≤ nr.1.val := by
  by_cases row : rs.2.val = 2
  · let x : Fin 8 := if rs.1.val = 3 then 4 else 3
    have width : 3 ≤ x.val ∧ x.val ≠ rs.1.val := by dsimp [x]; split <;> (try simp_all) <;> omega
    refine ⟨(x,2),?_,rfl,width.1⟩
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,row]
    dsimp
    simp <;> omega
  · refine ⟨(rs.1,2),?_,rfl,?_⟩
    · dsimp [HorizontalRook] at condition
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp
      simp <;> omega
    · dsimp [HorizontalRook] at condition
      change 3 ≤ rs.1.val
      omega

theorem horizontal_properties {rs : Square} (row : rs.2.val = 2) (width : 3 ≤ rs.1.val) :
    KRKSixGlobal.Region (3,1) rs (1,1) ∧ KRKSevenGeometry.Live (3,1) rs (1,1) ∧ SafeRook (3,1) rs (1,1) := by
  refine ⟨?_,?_,?_⟩
  · simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,KRKSixInwardCorner.GlobalRegion,KRKSixInterior.InnerCorner,
      KRKSixInwardCorner.Region,KRKSixInwardCorner.innerSym,symId,row]
    exact ⟨rfl,width⟩
  · refine ⟨((0 : Fin 8),0),?_⟩
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    dsimp
    omega
  · apply Or.inl
    dsimp [dInf,absDiff]
    omega

theorem horizontal_rook_clear {rs : Square} (condition : HorizontalRook rs) :
    KRKSevenGeometry.Clear (3,1) rs (1,1) := by
  obtain ⟨nr,sees,row,width⟩ := horizontal_line_sufficient condition
  have p := horizontal_properties row width
  apply KRKSevenReach.rook_step_clear sees
  · simp only [ne_iff_coords,row]
    dsimp
    omega
  · simp only [ne_iff_coords,row]
    dsimp
    omega
  · exact p.1
  · exact p.2.1
  · exact p.2.2

def Seven (sk rs : Square) : Prop :=
  (rs.2.val = 2 ∧ 3 ≤ rs.1.val ∧ dInf sk (3,1) = 1) ∨
  (rs.1.val = 2 ∧ 3 ≤ rs.2.val ∧ dInf sk (1,3) = 1) ∨
  (sk = ((3 : Fin 8),1) ∧ HorizontalRook rs) ∨
  (sk = ((1 : Fin 8),3) ∧ HorizontalRook (symSwap.f rs))

theorem necessary {sk rs : Square} (distinct : sk ≠ rs)
    (clear : KRKSevenGeometry.Clear sk rs (1,1)) : Seven sk rs := by
  rcases clear with immediate | ⟨i,distance,apart,far,region,live,safe⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region,live,safe⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · have actual : dInf sk ((KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i)) = 1 := by
      have preserved := (KRKSevenSlots.frame ((1 : Fin 8),1)).distance sk
        ((KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i))
      rw [(KRKSevenSlots.frame ((1 : Fin 8),1)).right_inv,distance] at preserved
      exact preserved.symm
    rcases inner_region region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩
    · have same : (KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i) = ((3 : Fin 8),1) :=
        Prod.ext (Fin.ext sx) (Fin.ext sy)
      exact Or.inl ⟨ry,rx,by rwa [same] at actual⟩
    · have same : (KRKSevenSlots.frame ((1 : Fin 8),1)).r (KRKSevenSlots.point i) = ((1 : Fin 8),3) :=
        Prod.ext (Fin.ext sx) (Fin.ext sy)
      exact Or.inr (Or.inl ⟨rx,ry,by rwa [same] at actual⟩)
  · have frameId : KRKSevenSlots.frame ((1 : Fin 8),1) = Frame.ofSym symId := by
      simp [KRKSevenSlots.frame,KRKEdgeDepth.depth,KRKSixInwardCorner.innerSym]
    rw [frameId] at sees region
    dsimp [Frame.ofSym,symId] at sees region
    rcases inner_region region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩
    · have same : sk = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      refine Or.inr (Or.inr (Or.inl ⟨same,?_⟩))
      exact horizontal_line_necessary (same ▸ distinct) (same ▸ sees) ry rx
    · have same : sk = ((1 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      refine Or.inr (Or.inr (Or.inr ⟨same,?_⟩))
      have mapped := (symSwap.sees_iff rs (a.target rs v) sk ((1 : Fin 8),1)).mpr sees
      have mappedApart : ((3 : Fin 8),1) ≠ symSwap.f rs := by
        have h := symSwap.ne_iff.mpr distinct
        rwa [same] at h
      apply horizontal_line_necessary mappedApart (nr := symSwap.f (a.target rs v))
      · simpa only [same,symSwap] using mapped
      · exact rx
      · exact ry

theorem swap_clear_iff {sk rs : Square} (distinct : sk ≠ rs) (notKing : sk ≠ ((1 : Fin 8),1))
    (notRook : rs ≠ ((1 : Fin 8),1)) (far : 2 ≤ dInf sk (1,1))
    (notCheck : ¬RookSees rs (1,1) sk (1,1)) :
    KRKSevenGeometry.Clear sk rs (1,1) ↔ KRKSevenGeometry.Clear (symSwap.f sk) (symSwap.f rs) (1,1) := by
  let g := Frame.ofSym symSwap
  constructor
  · exact KRKSevenReach.frame_map g distinct notKing notRook far notCheck
  · intro clear
    have back := KRKSevenReach.frame_map g (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing)
      (g.ne_iff.mpr notRook) (by simpa only [g.distance] using far)
      (fun h => notCheck ((g.sees _ _ _ _).mp h)) clear
    simpa only [g,Frame.ofSym,symSwap.invol] using back

theorem sufficient {sk rs : Square} (distinct : sk ≠ rs) (notKing : sk ≠ ((1 : Fin 8),1))
    (notRook : rs ≠ ((1 : Fin 8),1)) (far : 2 ≤ dInf sk (1,1))
    (notCheck : ¬RookSees rs (1,1) sk (1,1)) (seven : Seven sk rs) :
    KRKSevenGeometry.Clear sk rs (1,1) := by
  rcases seven with ⟨row,width,distance⟩ | ⟨file,height,distance⟩ | ⟨same,condition⟩ | ⟨same,condition⟩
  · have p := horizontal_properties row width
    apply KRKSevenReach.king_step_clear distance
    · simp only [ne_iff_coords,row]; dsimp; omega
    · decide
    · exact p.1
    · exact p.2.1
    · exact p.2.2
  · apply (swap_clear_iff distinct notKing notRook far notCheck).mpr
    have p := horizontal_properties (rs := symSwap.f rs) file height
    apply KRKSevenReach.king_step_clear (ns := ((3 : Fin 8),1))
    · have h := symSwap.dInf_eq sk ((1 : Fin 8),3)
      simpa only [symSwap] using h.trans distance
    · simp only [ne_iff_coords,symSwap,file]; dsimp; omega
    · decide
    · exact p.1
    · exact p.2.1
    · exact p.2.2
  · rw [same]
    exact horizontal_rook_clear condition
  · apply (swap_clear_iff distinct notKing notRook far notCheck).mpr
    rw [same]
    exact horizontal_rook_clear condition

theorem clear_iff {sk rs : Square} (distinct : sk ≠ rs) (notKing : sk ≠ ((1 : Fin 8),1))
    (notRook : rs ≠ ((1 : Fin 8),1)) (far : 2 ≤ dInf sk (1,1))
    (notCheck : ¬RookSees rs (1,1) sk (1,1)) : KRKSevenGeometry.Clear sk rs (1,1) ↔ Seven sk rs :=
  ⟨necessary distinct,sufficient distinct notKing notRook far notCheck⟩

theorem kernel_seven_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk (1,1)) (notCheck : ¬RookSees rs (1,1) sk (1,1)) : MateWithin σ 7 q ↔ Seven sk rs :=
  (KRKSevenGeometry.kernel_seven_iff material turn far notCheck).trans
    (clear_iff material.1 material.2.1 material.2.2.1 far notCheck)

end EndgameChess.Rules.KRKSevenInner
