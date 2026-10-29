import EndgameChess.Rules.KRKEightInteriorExact

namespace EndgameChess.Rules.KRKSevenSecond
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

inductive Kind where
  | west | middle | east

def king : Kind → Square
  | .west => (1,2)
  | .middle => (2,2)
  | .east => (3,2)

def RookRegion (rs : Square) : Kind → Prop
  | .west => rs.1.val = 3 ∧ 2 ≤ rs.2.val
  | .middle => 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 3 ≤ rs.1.val) ∨
      (rs.2.val = 1 ∧ (rs.1.val = 3 ∨ rs.1.val = 4))
  | .east => (rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨ (rs.2.val = 1 ∧ 4 ≤ rs.1.val)

def RookCondition (rs : Square) : Kind → Prop
  | .west => rs.1.val = 3 ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 2 ≤ rs.1.val)
  | .middle | .east => True

theorem shape_iff {sk rs : Square} : KRKSixSecond.Region sk rs ↔
    ∃ i : Kind, sk = king i ∧ RookRegion rs i := by
  constructor
  · rintro ⟨sy,⟨sx,region⟩ | ⟨sx,region⟩ | ⟨sx,region⟩⟩
    · exact ⟨.west,Prod.ext (Fin.ext sx) (Fin.ext sy),region⟩
    · exact ⟨.middle,Prod.ext (Fin.ext sx) (Fin.ext sy),region⟩
    · exact ⟨.east,Prod.ext (Fin.ext sx) (Fin.ext sy),region⟩
  · rintro ⟨i,rfl,region⟩
    cases i with
    | west => exact ⟨rfl,Or.inl ⟨rfl,region⟩⟩
    | middle => exact ⟨rfl,Or.inr (Or.inl ⟨rfl,region⟩)⟩
    | east => exact ⟨rfl,Or.inr (Or.inr ⟨rfl,region⟩)⟩

theorem global_region_iff {sk rs : Square} : KRKSixGlobal.Region sk rs (2,0) ↔ KRKSixSecond.Region sk rs := by
  simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,KRKSixGlobal.EdgeRegion]

theorem frame_f (s : Square) : (KRKSevenSlots.frame ((2 : Fin 8),0)).f s = s := by
  simp [KRKSevenSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId]

theorem frame_r (s : Square) : (KRKSevenSlots.frame ((2 : Fin 8),0)).r s = s := by
  simp [KRKSevenSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId]

theorem properties {rs : Square} {i : Kind} (region : RookRegion rs i) :
    king i ≠ rs ∧ 2 ≤ dInf (king i) (2,0) ∧
      KRKSevenGeometry.Live (king i) rs (2,0) ∧ SafeRook (king i) rs (2,0) := by
  have live : KRKSevenGeometry.Live (king i) rs (2,0) := by
    let t : Square := if rs.1.val = 1 then (3,0) else (1,0)
    refine ⟨t,?_⟩
    cases i <;> dsimp [RookRegion] at region <;> dsimp [t] <;> split <;>
      simp only [king,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] <;>
      simp <;> omega
  refine ⟨?_,?_,live,?_⟩
  · cases i <;> dsimp [RookRegion] at region <;> simp only [king,ne_iff_coords] <;> dsimp <;> omega
  · cases i <;> decide
  · cases i <;> dsimp [RookRegion] at region <;> dsimp [king,SafeRook,dInf,absDiff] <;> omega

def KingEntries (sk rs : Square) : Prop :=
  ∃ i : Kind, RookRegion rs i ∧ dInf sk (king i) = 1

theorem king_points_iff {sk rs : Square} : KRKSevenGeometry.KingPoints sk rs (2,0) ↔ KingEntries sk rs := by
  simp only [KRKSevenGeometry.KingPoints,frame_f,frame_r]
  constructor
  · rintro ⟨j,distance,_,_,region,_,_⟩
    obtain ⟨i,equal,condition⟩ := shape_iff.mp (global_region_iff.mp region)
    rw [equal] at distance
    exact ⟨i,condition,distance⟩
  · rintro ⟨i,condition,distance⟩
    have region := global_region_iff.mpr (shape_iff.mpr ⟨i,rfl,condition⟩)
    obtain ⟨j,equal⟩ := KRKSevenSlots.region_point region
    rw [frame_f] at equal
    have p := properties condition
    exact ⟨j,equal ▸ distance,equal ▸ p.1,equal ▸ p.2.1,
      equal ▸ region,equal ▸ p.2.2.1,equal ▸ p.2.2.2⟩

private theorem positive_rank {rs : Square} {i : Kind}
    (notWeak : rs ≠ ((2 : Fin 8),0))
    (notCheck : ¬RookSees rs (2,0) (king i) (2,0)) : 1 ≤ rs.2.val := by
  cases i <;> simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at notWeak notCheck <;>
    dsimp at notWeak notCheck <;> omega

private theorem west_line_necessary {rs nr : Square} (apart : king .west ≠ rs)
    (sees : RookSees rs nr (king .west) (2,0)) (region : RookRegion nr .west) :
    RookCondition rs .west := by
  dsimp [RookRegion] at region
  simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart
  dsimp [RookCondition] at *
  omega

theorem rook_destination {rs : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((2 : Fin 8),0)) (notCheck : ¬RookSees rs (2,0) (king i) (2,0))
    (condition : RookCondition rs i) : ∃ nr, RookSees rs nr (king i) (2,0) ∧ RookRegion nr i := by
  have height := positive_rank notWeak notCheck
  cases i with
  | west =>
    let nr : Square := if rs.1.val = 3 then (3,if rs.2.val = 2 then 3 else 2) else (3,rs.2)
    refine ⟨nr,?_,?_⟩
    · dsimp [nr]; split <;> (try split) <;>
        simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] <;>
        dsimp [RookCondition] at condition <;> simp <;> omega
    · dsimp [nr]; split <;> (try split) <;> dsimp [RookRegion,RookCondition] at * <;> omega
  | middle =>
    let nr : Square := if rs.2.val = 1 then (if rs.1.val = 3 then 4 else 3,1)
      else if rs.2.val = 2 then (rs.1,3) else (if rs.1.val = 0 then 1 else 0,rs.2)
    refine ⟨nr,?_,?_⟩
    · simp only [king,ne_iff_coords] at apart
      dsimp [nr]; split <;> split <;> (try split) <;>
        simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] <;> simp <;> omega
    · dsimp [nr]; split <;> split <;> (try split) <;> dsimp [RookRegion] <;> (try simp) <;> omega
  | east =>
    let nr : Square := if rs.2.val = 1 then (if rs.1.val = 4 then 5 else 4,1)
      else if rs.1.val = 1 then (1,if rs.2.val = 2 then 3 else 2)
      else if 3 ≤ rs.2.val ∨ rs.1.val ≤ 2 then (1,rs.2) else (rs.1,1)
    refine ⟨nr,?_,?_⟩
    · simp only [king,ne_iff_coords] at apart
      dsimp [nr]; split <;> split <;> (try split) <;>
        simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] <;> simp <;> omega
    · simp only [king,ne_iff_coords] at apart
      dsimp [nr]; split <;> split <;> (try split) <;> dsimp [RookRegion] <;> (try simp) <;>
        first | trivial | omega

def RookEntries (sk rs : Square) : Prop := ∃ i : Kind, sk = king i ∧ RookCondition rs i

theorem rook_rays_iff {sk rs : Square} (apart : sk ≠ rs) (notWeak : rs ≠ ((2 : Fin 8),0))
    (notCheck : ¬RookSees rs (2,0) sk (2,0)) :
    KRKSevenGeometry.RookRays sk rs (2,0) ↔ RookEntries sk rs := by
  simp only [KRKSevenGeometry.RookRays,frame_f,frame_r]
  constructor
  · rintro ⟨j,_,a,v,sees,_,_,region,_,_⟩
    obtain ⟨i,equal,condition⟩ := shape_iff.mp (global_region_iff.mp region)
    refine ⟨i,equal,?_⟩
    cases i with
    | west => exact west_line_necessary (equal ▸ apart) (equal ▸ sees) condition
    | middle => trivial
    | east => trivial
  · rintro ⟨i,rfl,condition⟩
    obtain ⟨nr,sees,region⟩ := rook_destination apart notWeak notCheck condition
    have p := properties region
    have global := global_region_iff.mpr (shape_iff.mpr ⟨i,rfl,region⟩)
    obtain ⟨j,equal⟩ := KRKSevenSlots.region_point global
    rw [frame_f] at equal
    obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target sees.1
    have notWeakTarget : nr ≠ ((2 : Fin 8),0) := by
      cases i <;> dsimp [RookRegion] at region <;> simp only [ne_iff_coords] <;> dsimp <;> omega
    rw [target] at sees global
    exact ⟨j,equal,a,v,sees,target ▸ p.1.symm,target ▸ notWeakTarget,
      global,target ▸ p.2.2.1,target ▸ p.2.2.2⟩

def Seven (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (notWeak : rs ≠ ((2 : Fin 8),0))
    (notCheck : ¬RookSees rs (2,0) sk (2,0)) : KRKSevenGeometry.Clear sk rs (2,0) ↔ Seven sk rs := by
  constructor
  · rintro (immediate | points | rays)
    · have geometry := (KRKThreePly.immediate_middle_iff (wk := ((2 : Fin 8),0)) rfl (by decide) (by decide)).mp immediate
      exact Or.inr ⟨.middle,Prod.ext (Fin.ext geometry.1) (Fin.ext geometry.2.1),True.intro⟩
    · exact Or.inl (king_points_iff.mp points)
    · exact Or.inr ((rook_rays_iff apart notWeak notCheck).mp rays)
  · rintro (points | rays)
    · exact Or.inr (Or.inl (king_points_iff.mpr points))
    · exact Or.inr (Or.inr ((rook_rays_iff apart notWeak notCheck).mpr rays))

theorem kernel_seven_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (2,0)) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk (2,0)) (notCheck : ¬RookSees rs (2,0) sk (2,0)) :
    MateWithin σ 7 q ↔ Seven sk rs :=
  (KRKSevenGeometry.kernel_seven_iff material turn far notCheck).trans
    (clear_iff material.1 material.2.2.1 notCheck)

end EndgameChess.Rules.KRKSevenSecond
