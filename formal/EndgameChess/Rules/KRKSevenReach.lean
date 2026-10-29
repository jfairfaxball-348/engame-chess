import EndgameChess.Rules.KRKSevenGeometry

namespace EndgameChess.Rules.KRKSevenReach
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 300000

theorem region_weak_domain {sk rs wk : Square} (region : KRKSixGlobal.Region sk rs wk) :
    KRKEdgeDepth.depth wk = 0 ∨ KRKSixInterior.InnerCorner wk := by
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · exact Or.inl edge
  · simp only [KRKSixGlobal.Region,edge,↓reduceIte] at region
    exact Or.inr region.1

theorem region_interior_distance {sk rs wk : Square} (inside : 0 < KRKEdgeDepth.depth wk)
    (region : KRKSixGlobal.Region sk rs wk) : dInf sk wk = 2 := by
  have edge : ¬KRKEdgeDepth.depth wk = 0 := by omega
  simp only [KRKSixGlobal.Region,edge,↓reduceIte] at region
  have spec := KRKSixInwardCorner.inner_sym_spec region.1
  have mapped : dInf ((KRKSixInwardCorner.innerSym wk).f sk) ((KRKSixInwardCorner.innerSym wk).f wk) = 2 := by
    rw [spec]
    rcases region.2 with ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩ <;>
      simp only [dInf,absDiff,sx,sy] <;> omega
  rwa [(KRKSixInwardCorner.innerSym wk).dInf_eq] at mapped

theorem weak_domain {sk rs wk : Square} (clear : KRKSevenGeometry.Clear sk rs wk) :
    KRKEdgeDepth.depth wk = 0 ∨ KRKSixInterior.InnerCorner wk := by
  rcases clear with immediate | ⟨i,_,_,_,region,_⟩ | ⟨i,_,a,v,_,_,_,region,_⟩
  · exact Or.inl (KRKFourPlyEscape.three_depth_zero (Or.inl immediate))
  · exact region_weak_domain region
  · exact region_weak_domain region

theorem interior_king_near {sk rs wk : Square} (inside : 0 < KRKEdgeDepth.depth wk)
    (clear : KRKSevenGeometry.Clear sk rs wk) : KRKSixInterior.InnerCorner wk ∧ dInf sk wk ≤ 3 := by
  have inner : KRKSixInterior.InnerCorner wk := (weak_domain clear).resolve_left (by omega)
  refine ⟨inner,?_⟩
  rcases clear with immediate | ⟨i,distance,_,_,region,_⟩ | ⟨i,_,a,v,_,_,_,region,_⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    omega
  · have destDistance := region_interior_distance inside region
    have actualDistance : dInf sk ((KRKSevenSlots.frame wk).r (KRKSevenSlots.point i)) = 1 := by
      have preserved := (KRKSevenSlots.frame wk).distance sk ((KRKSevenSlots.frame wk).r (KRKSevenSlots.point i))
      rw [(KRKSevenSlots.frame wk).right_inv,distance] at preserved
      exact preserved.symm
    simp only [dInf,absDiff] at actualDistance destDistance ⊢
    omega
  · have distance := region_interior_distance inside region
    omega

theorem frame_map (g : Frame) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (clear : KRKSevenGeometry.Clear sk rs wk) : KRKSevenGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by
  let q := krkPos .white sk rs wk .white
  let r := krkPos .white (g.f sk) (g.f rs) (g.f wk) .white
  have material : IsKRK q .white sk rs wk := ⟨distinct,notKing,notRook,rfl⟩
  have mapped : IsKRK r .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr distinct,g.ne_iff.mpr notKing,g.ne_iff.mpr notRook,rfl⟩
  have win := (KRKSevenGeometry.kernel_seven_iff material rfl far notCheck).mpr clear
  have transported := KRKFrameBound.bound_transport g
    (show Matches q .white ⟨sk,rs,wk,true⟩ from ⟨material,rfl⟩) rfl
    (show Matches r .white (g.mapState ⟨sk,rs,wk,true⟩) from ⟨mapped,rfl⟩) win
  exact (KRKSevenGeometry.kernel_seven_iff mapped rfl (by rwa [g.distance])
    (fun seen => notCheck ((g.sees _ _ _ _).mp seen))).mp transported

theorem king_step_clear {sk rs wk ns : Square} (distance : dInf sk ns = 1) (apart : ns ≠ rs)
    (far : 2 ≤ dInf ns wk) (region : KRKSixGlobal.Region ns rs wk)
    (live : KRKSevenGeometry.Live ns rs wk) (safe : SafeRook ns rs wk) : KRKSevenGeometry.Clear sk rs wk := by
  obtain ⟨i,equal⟩ := KRKSevenSlots.region_point region
  have actual := (KRKSevenSlots.frame wk).preimage_eq equal
  have mappedDistance := (KRKSevenSlots.frame wk).distance sk ns
  rw [equal,distance] at mappedDistance
  have mappedFar : 2 ≤ dInf (KRKSevenSlots.point i) ((KRKSevenSlots.frame wk).f wk) := by
    rw [←equal,(KRKSevenSlots.frame wk).distance]
    exact far
  have mappedApart : KRKSevenSlots.point i ≠ (KRKSevenSlots.frame wk).f rs := by
    rw [←equal]
    exact (KRKSevenSlots.frame wk).ne_iff.mpr apart
  rw [actual] at region live safe
  exact Or.inr (Or.inl ⟨i,mappedDistance,mappedApart,mappedFar,region,live,safe⟩)

theorem rook_step_clear {sk rs wk nr : Square} (sees : RookSees rs nr sk wk)
    (notKing : nr ≠ sk) (notWeak : nr ≠ wk) (region : KRKSixGlobal.Region sk nr wk)
    (live : KRKSevenGeometry.Live sk nr wk) (safe : SafeRook sk nr wk) : KRKSevenGeometry.Clear sk rs wk := by
  obtain ⟨i,equal⟩ := KRKSevenSlots.region_point region
  have mappedSees := ((KRKSevenSlots.frame wk).sees rs nr sk wk).mpr sees
  obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
  have actual := (KRKSevenSlots.frame wk).preimage_eq target
  have apartKing : a.target ((KRKSevenSlots.frame wk).f rs) v ≠ (KRKSevenSlots.frame wk).f sk := by
    rw [←target]
    exact (KRKSevenSlots.frame wk).ne_iff.mpr notKing
  have apartWeak : a.target ((KRKSevenSlots.frame wk).f rs) v ≠ (KRKSevenSlots.frame wk).f wk := by
    rw [←target]
    exact (KRKSevenSlots.frame wk).ne_iff.mpr notWeak
  rw [target] at mappedSees
  rw [actual] at region live safe
  exact Or.inr (Or.inr ⟨i,equal,a,v,mappedSees,apartKing,apartWeak,region,live,safe⟩)

end EndgameChess.Rules.KRKSevenReach
