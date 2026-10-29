import EndgameChess.Rules.KRKSevenMiddle

namespace EndgameChess.Rules.KRKSevenNear
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

private theorem val0 : ((0 : Fin 8).val) = 0 := rfl
private theorem val1 : ((1 : Fin 8).val) = 1 := rfl
private theorem val2 : ((2 : Fin 8).val) = 2 := rfl
private theorem val3 : ((3 : Fin 8).val) = 3 := rfl
private theorem val4 : ((4 : Fin 8).val) = 4 := rfl

inductive Kind where
  | west | middle | diagonal | low | side | high

def king : Kind → Square
  | .west => (0,2)
  | .middle => (1,2)
  | .diagonal => (2,2)
  | .low => (3,0)
  | .side => (3,1)
  | .high => (3,2)

def LowRegion (rs : Square) : Prop :=
  (rs.2.val = 1 ∧ 3 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ (rs.2.val = 2 ∨ rs.2.val = 3))

def SideRegion (rs : Square) : Prop :=
  (rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨ (rs.1.val = 2 ∧ rs.2.val = 1)

def RookRegion (rs : Square) : Kind → Prop
  | .west => rs.1.val = 2 ∧ 2 ≤ rs.2.val
  | .middle => 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨
      (rs.2.val = 1 ∧ (rs.1.val = 2 ∨ rs.1.val = 3))
  | .diagonal => True
  | .low => LowRegion rs
  | .side | .high => SideRegion rs

theorem shape_iff {sk rs : Square} : KRKSixNear.Region sk rs ↔
    ∃ i : Kind, sk = king i ∧ RookRegion rs i := by
  constructor
  · rintro (⟨sy,⟨sx,h⟩ | ⟨sx,h⟩ | ⟨sx,h⟩⟩ | extra)
    · exact ⟨.west,Prod.ext (Fin.ext sx) (Fin.ext sy),h⟩
    · exact ⟨.middle,Prod.ext (Fin.ext sx) (Fin.ext sy),h⟩
    · exact ⟨.diagonal,Prod.ext (Fin.ext sx) (Fin.ext sy),True.intro⟩
    · rcases extra with ⟨sx,sy⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩
      · exact ⟨.diagonal,Prod.ext (Fin.ext sx) (Fin.ext sy),True.intro⟩
      · exact ⟨.low,Prod.ext (Fin.ext sx) (Fin.ext sy),h⟩
      · exact ⟨.side,Prod.ext (Fin.ext sx) (Fin.ext sy),h⟩
      · exact ⟨.high,Prod.ext (Fin.ext sx) (Fin.ext sy),h⟩
  · rintro ⟨i,rfl,h⟩
    cases i with
    | west => exact Or.inl ⟨rfl,Or.inl ⟨rfl,h⟩⟩
    | middle => exact Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,h⟩)⟩
    | diagonal => exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    | low => exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,h⟩))
    | side => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,h⟩)))
    | high => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,h⟩)))

theorem king_far (i : Kind) : 2 ≤ dInf (king i) ((1 : Fin 8),0) := by cases i <;> decide

theorem slot_properties {rs : Square} {i : Kind} (notDiagonal : i ≠ .diagonal) (region : RookRegion rs i) :
    king i ≠ rs ∧ KRKSevenGeometry.Live (king i) rs (1,0) ∧ SafeRook (king i) rs (1,0) := by
  cases i with
  | west =>
    have p := KRKFiveNear.near_slot_properties (wk := ((1 : Fin 8),0)) rfl rfl
      (i := .nearWest) rfl region
    exact ⟨p.1,p.2.2.1,p.2.2.2⟩
  | middle =>
    have p := KRKFiveNear.near_slot_properties (wk := ((1 : Fin 8),0)) rfl rfl
      (i := .nearMiddle) rfl region
    exact ⟨p.1,p.2.2.1,p.2.2.2⟩
  | diagonal => exact False.elim (notDiagonal rfl)
  | low =>
    have live : KRKSevenGeometry.Live (king .low) rs (1,0) := by
      refine ⟨((0 : Fin 8),0),?_⟩
      dsimp [RookRegion,LowRegion] at region
      simp only [king,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,
        val0,val1,val2,val3]
      omega
    refine ⟨?_,live,?_⟩ <;> dsimp [RookRegion,LowRegion] at region <;>
      simp only [king,SafeRook,dInf,absDiff,ne_iff_coords,val0,val1,val2,val3] <;> omega
  | side =>
    have live : KRKSevenGeometry.Live (king .side) rs (1,0) := by
      refine ⟨((0 : Fin 8),0),?_⟩
      dsimp [RookRegion,SideRegion] at region
      simp only [king,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,
        val0,val1,val2,val3]
      omega
    refine ⟨?_,live,?_⟩ <;> dsimp [RookRegion,SideRegion] at region <;>
      simp only [king,SafeRook,dInf,absDiff,ne_iff_coords,val0,val1,val2,val3] <;> omega
  | high =>
    have live : KRKSevenGeometry.Live (king .high) rs (1,0) := by
      refine ⟨((0 : Fin 8),0),?_⟩
      dsimp [RookRegion,SideRegion] at region
      simp only [king,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,
        val0,val1,val2,val3]
      omega
    refine ⟨?_,live,?_⟩ <;> dsimp [RookRegion,SideRegion] at region <;>
      simp only [king,SafeRook,dInf,absDiff,ne_iff_coords,val0,val1,val2,val3] <;> omega

theorem diagonal_live {rs : Square} (safe : SafeRook ((2 : Fin 8),2) rs (1,0)) :
    KRKSevenGeometry.Live (2,2) rs (1,0) := by
  by_cases row : rs.2.val = 0
  · refine ⟨((0 : Fin 8),1),?_⟩
    simp only [SafeRook,dInf,absDiff,row,val0,val1,val2] at safe
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row,
      val0,val1,val2]
    omega
  by_cases file : rs.1.val = 0
  · refine ⟨((2 : Fin 8),0),?_⟩
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,file,
      val0,val1,val2]
    omega
  · refine ⟨((0 : Fin 8),0),?_⟩
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,
      val0,val1,val2]
    omega

theorem slot_live {rs : Square} {i : Kind} (region : RookRegion rs i) (safe : SafeRook (king i) rs (1,0)) :
    KRKSevenGeometry.Live (king i) rs (1,0) := by
  by_cases diagonal : i = .diagonal
  · subst i; exact diagonal_live safe
  · exact (slot_properties diagonal region).2.1

private theorem frame_f (s : Square) : (KRKSevenSlots.frame ((1 : Fin 8),0)).f s = s := rfl
private theorem frame_r (s : Square) : (KRKSevenSlots.frame ((1 : Fin 8),0)).r s = s := rfl

theorem global_region_iff {sk rs : Square} : KRKSixGlobal.Region sk rs (1,0) ↔ KRKSixNear.Region sk rs := by
  simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,KRKSixGlobal.EdgeRegion,
    val0,val1,val2,val3]

def KingEntries (sk rs : Square) : Prop :=
  ∃ i : Kind, RookRegion rs i ∧ dInf sk (king i) = 1 ∧ king i ≠ rs ∧ SafeRook (king i) rs (1,0)

theorem king_points_iff {sk rs : Square} : KRKSevenGeometry.KingPoints sk rs (1,0) ↔ KingEntries sk rs := by
  simp only [KRKSevenGeometry.KingPoints,frame_f,frame_r]
  constructor
  · rintro ⟨j,distance,apart,_,region,_,safe⟩
    obtain ⟨i,equal,shape⟩ := shape_iff.mp (global_region_iff.mp region)
    rw [equal] at distance apart safe
    exact ⟨i,shape,distance,apart,safe⟩
  · rintro ⟨i,region,distance,apart,safe⟩
    have shape := global_region_iff.mpr (shape_iff.mpr ⟨i,rfl,region⟩)
    obtain ⟨j,equal⟩ := KRKSevenSlots.region_point shape
    rw [frame_f] at equal
    rw [equal] at distance apart safe shape
    have far := king_far i
    have live := slot_live region (by rwa [←equal] at safe)
    rw [equal] at far live
    exact ⟨j,distance,apart,far,shape,live,safe⟩

def Reach (rs : Square) (i : Kind) : Prop :=
  ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
    RookSees rs (a.target rs v) (king i) (1,0) ∧ RookRegion (a.target rs v) i ∧
      a.target rs v ≠ king i ∧ SafeRook (king i) (a.target rs v) (1,0)

def RookCondition (rs : Square) : Kind → Prop
  | .west => rs.1.val = 2 ∨ 2 ≤ rs.2.val
  | .middle | .diagonal => True
  | .low => 3 ≤ rs.1.val ∨ (1 ≤ rs.2.val ∧ rs.2.val ≤ 3)
  | .side => 2 ≤ rs.2.val ∨ (rs.1.val = 0 ∧ rs.2.val = 1)
  | .high => 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ rs.1.val ≤ 2) ∨ (rs.2.val = 1 ∧ rs.1.val ≠ 2)

private theorem build_reach {rs : Square} {i : Kind} {a : KRKCornerSlotBarriers.Axis} {v : Fin 8}
    (notDiagonal : i ≠ .diagonal) (sees : RookSees rs (a.target rs v) (king i) (1,0))
    (region : RookRegion (a.target rs v) i) : Reach rs i := by
  have p := slot_properties notDiagonal region
  exact ⟨a,v,sees,region,p.1.symm,p.2.2⟩

private theorem not_file_one {sk rs : Square} (sx : sk.1.val = 3) (notWeak : rs ≠ ((1 : Fin 8),0))
    (notCheck : ¬RookSees rs (1,0) sk (1,0)) : rs.1.val ≠ 1 := by
  simp only [RookSees,RookLine,OnSeg,ne_iff_coords,sx,val0,val1] at notCheck notWeak
  omega

private theorem positive_rank {sk rs : Square} (sx : sk.1.val = 3) (sy : 1 ≤ sk.2.val)
    (notWeak : rs ≠ ((1 : Fin 8),0)) (notCheck : ¬RookSees rs (1,0) sk (1,0)) : 1 ≤ rs.2.val := by
  simp only [RookSees,RookLine,OnSeg,ne_iff_coords,sx,val0,val1] at notCheck notWeak
  omega

theorem low_reach_iff {rs : Square} (notWeak : rs ≠ ((1 : Fin 8),0))
    (notCheck : ¬RookSees rs (1,0) (king .low) (1,0)) : Reach rs .low ↔ RookCondition rs .low := by
  have notOne := not_file_one (sk := king .low) rfl notWeak notCheck
  constructor
  · rintro ⟨a,v,sees,region,_,_⟩
    cases a <;>
      simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,RookRegion,LowRegion,
        ne_iff_coords,val0,val1,val2,val3] at sees region <;>
      (try simp at sees region) <;>
      (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4] at *) <;>
      dsimp [RookCondition] <;> (try simp only [king,ne_iff_coords,val0,val1,val2,val3] at apart) <;> omega
  · intro condition
    by_cases tallFile : 3 ≤ rs.1.val
    · by_cases row : rs.2.val = 1
      · let v : Fin 8 := if rs.1.val = 3 then 4 else 3
        have width : 3 ≤ v.val ∧ v.val ≠ rs.1.val := by dsimp [v]; split <;> simp_all <;> omega
        apply build_reach (i := .low) (a := .rank) (v := v) (by intro h; cases h)
        · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,row,val0,val1,val3]
          simp <;> omega
        · change (rs.2.val = 1 ∧ 3 ≤ v.val) ∨ (v.val = 1 ∧ (rs.2.val = 2 ∨ rs.2.val = 3))
          exact Or.inl ⟨row,width.1⟩
      · apply build_reach (i := .low) (a := .file) (v := 1) (by intro h; cases h)
        · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,val0,val1,val3]
          simp <;> omega
        · change (((1 : Fin 8).val) = 1 ∧ 3 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ (_ = 2 ∨ _ = 3))
          exact Or.inl ⟨rfl,tallFile⟩
    · have height : 1 ≤ rs.2.val ∧ rs.2.val ≤ 3 := by exact condition.resolve_left tallFile
      by_cases row : rs.2.val = 1
      · apply build_reach (i := .low) (a := .rank) (v := 3) (by intro h; cases h)
        · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,row,val0,val1,val3]
          simp <;> omega
        · change (rs.2.val = 1 ∧ 3 ≤ (3 : Fin 8).val) ∨ _
          exact Or.inl ⟨row,by decide⟩
      · apply build_reach (i := .low) (a := .rank) (v := 1) (by intro h; cases h)
        · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,val0,val1,val3]
          simp <;> omega
        · change (rs.2.val = 1 ∧ 3 ≤ (1 : Fin 8).val) ∨ ((1 : Fin 8).val = 1 ∧ (rs.2.val = 2 ∨ rs.2.val = 3))
          exact Or.inr ⟨rfl,by omega⟩

theorem side_reach_iff {rs : Square} (apart : king .side ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),0))
    (notCheck : ¬RookSees rs (1,0) (king .side) (1,0)) : Reach rs .side ↔ RookCondition rs .side := by
  have notOne := not_file_one (sk := king .side) rfl notWeak notCheck
  have height := positive_rank (sk := king .side) rfl (by decide) notWeak notCheck
  constructor
  · rintro ⟨a,v,sees,region,_,_⟩
    cases a <;>
      simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,RookRegion,SideRegion,
        ne_iff_coords,val0,val1,val2,val3] at sees region <;>
      (try simp at sees region) <;>
      (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4] at *) <;>
      dsimp [RookCondition] <;> (try simp only [king,ne_iff_coords,val0,val1,val2,val3] at apart) <;> omega
  · intro condition
    rcases condition with tall | ⟨file,row⟩
    · apply build_reach (i := .side) (a := .rank) (v := 1) (by intro h; cases h)
      · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,val0,val1,val3]
        simp <;> omega
      · change ((1 : Fin 8).val = 1 ∧ 2 ≤ rs.2.val) ∨ _
        exact Or.inl ⟨rfl,tall⟩
    · apply build_reach (i := .side) (a := .rank) (v := 2) (by intro h; cases h)
      · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,file,row,val0,val1,val2,val3]
        simp
      · change (_ ∧ _) ∨ ((2 : Fin 8).val = 2 ∧ rs.2.val = 1)
        exact Or.inr ⟨rfl,row⟩

theorem high_reach_iff {rs : Square} (apart : king .high ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),0))
    (notCheck : ¬RookSees rs (1,0) (king .high) (1,0)) : Reach rs .high ↔ RookCondition rs .high := by
  have notOne := not_file_one (sk := king .high) rfl notWeak notCheck
  have height := positive_rank (sk := king .high) rfl (by decide) notWeak notCheck
  constructor
  · rintro ⟨a,v,sees,region,_,_⟩
    cases a <;>
      simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,RookRegion,SideRegion,
        ne_iff_coords,val0,val1,val2,val3] at sees region <;>
      (try simp at sees region) <;>
      (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4] at *) <;>
      dsimp [RookCondition] <;> (try simp only [king,ne_iff_coords,val0,val1,val2,val3] at apart) <;> omega
  · intro condition
    rcases condition with tall | ⟨row,file⟩ | ⟨row,file⟩
    · apply build_reach (i := .high) (a := .rank) (v := 1) (by intro h; cases h)
      · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,val0,val1,val2,val3]
        simp <;> omega
      · change ((1 : Fin 8).val = 1 ∧ 2 ≤ rs.2.val) ∨ _
        exact Or.inl ⟨rfl,by omega⟩
    · apply build_reach (i := .high) (a := .rank) (v := 1) (by intro h; cases h)
      · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,row,val0,val1,val2,val3]
        simp <;> omega
      · change ((1 : Fin 8).val = 1 ∧ 2 ≤ rs.2.val) ∨ _
        exact Or.inl ⟨rfl,by omega⟩
    · apply build_reach (i := .high) (a := .rank) (v := 2) (by intro h; cases h)
      · simp only [KRKCornerSlotBarriers.Axis.target,king,RookSees,RookLine,OnSeg,ne_iff_coords,row,val0,val1,val2,val3]
        simp <;> omega
      · change (_ ∧ _) ∨ ((2 : Fin 8).val = 2 ∧ rs.2.val = 1)
        exact Or.inr ⟨rfl,row⟩

theorem reach_iff {rs : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((1 : Fin 8),0)) (notCheck : ¬RookSees rs (1,0) (king i) (1,0)) :
    Reach rs i ↔ RookCondition rs i := by
  cases i with
  | west =>
    constructor
    · rintro ⟨a,v,sees,region,_,_⟩
      exact (KRKFiveNear.west_reachable_iff rfl rfl rfl apart).mp ⟨a,v,sees,region⟩
    · intro condition
      obtain ⟨a,v,sees,region⟩ := (KRKFiveNear.west_reachable_iff (wk := ((1 : Fin 8),0)) rfl rfl rfl apart).mpr condition
      exact build_reach (by intro h; cases h) sees region
  | middle =>
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨a,v,sees,region⟩ := KRKFiveNear.middle_reachable rfl rfl rfl notWeak notCheck
      exact build_reach (by intro h; cases h) sees region
  | diagonal =>
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨a,v,sees,region⟩ := KRKFiveNear.east_reachable rfl rfl rfl apart notWeak
      have props := KRKFiveNear.near_slot_properties (wk := ((1 : Fin 8),0)) rfl rfl
        (i := .nearEast) rfl region
      exact ⟨a,v,sees,True.intro,props.1.symm,props.2.2.2⟩
  | low => exact low_reach_iff notWeak notCheck
  | side => exact side_reach_iff apart notWeak notCheck
  | high => exact high_reach_iff apart notWeak notCheck

def RookEntries (sk rs : Square) : Prop := ∃ i : Kind, sk = king i ∧ RookCondition rs i

theorem rook_rays_iff {sk rs : Square} (apart : sk ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),0))
    (notCheck : ¬RookSees rs (1,0) sk (1,0)) :
    KRKSevenGeometry.RookRays sk rs (1,0) ↔ RookEntries sk rs := by
  simp only [KRKSevenGeometry.RookRays,frame_f,frame_r]
  constructor
  · rintro ⟨j,_,a,v,sees,notKing,_,region,_,safe⟩
    obtain ⟨i,equal,shape⟩ := shape_iff.mp (global_region_iff.mp region)
    refine ⟨i,equal,?_⟩
    rw [equal] at apart notCheck sees notKing safe
    exact (reach_iff apart notWeak notCheck).mp ⟨a,v,sees,shape,notKing,safe⟩
  · rintro ⟨i,rfl,condition⟩
    obtain ⟨a,v,sees,region,notKing,safe⟩ := (reach_iff apart notWeak notCheck).mpr condition
    have global := global_region_iff.mpr (shape_iff.mpr ⟨i,rfl,region⟩)
    obtain ⟨j,equal⟩ := KRKSevenSlots.region_point global
    rw [frame_f] at equal
    have notWeakTarget : a.target rs v ≠ ((1 : Fin 8),0) := by
      intro same
      rw [same] at safe
      have far := king_far i
      have zero : dInf ((1 : Fin 8),0) (1,0) = 0 := by decide
      simp only [SafeRook,zero] at safe
      omega
    exact ⟨j,equal,a,v,sees,notKing,notWeakTarget,global,slot_live region safe,safe⟩

/-- Six explicit king destinations, plus evaluated rook-line conditions. -/
def Seven (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),0))
    (notCheck : ¬RookSees rs (1,0) sk (1,0)) : KRKSevenGeometry.Clear sk rs (1,0) ↔ Seven sk rs := by
  constructor
  · rintro (mate | points | rays)
    · have equal := KRKThreePly.immediate_near_iff rfl rfl |>.mp mate
      exact Or.inr ⟨.middle,Prod.ext (Fin.ext equal.1) (Fin.ext equal.2.1),True.intro⟩
    · exact Or.inl (king_points_iff.mp points)
    · exact Or.inr ((rook_rays_iff apart notWeak notCheck).mp rays)
  · rintro (points | rays)
    · exact Or.inr (Or.inl (king_points_iff.mpr points))
    · exact Or.inr (Or.inr ((rook_rays_iff apart notWeak notCheck).mpr rays))

theorem kernel_seven_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,0)) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk (1,0)) (notCheck : ¬RookSees rs (1,0) sk (1,0)) :
    MateWithin σ 7 q ↔ Seven sk rs :=
  (KRKSevenGeometry.kernel_seven_iff material turn far notCheck).trans
    (clear_iff material.1 material.2.2.1 notCheck)

end EndgameChess.Rules.KRKSevenNear
