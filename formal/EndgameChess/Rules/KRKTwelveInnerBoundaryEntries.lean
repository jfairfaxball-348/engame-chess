import EndgameChess.Rules.KRKTwelveInnerHigh

namespace EndgameChess.Rules.KRKTwelveInnerBoundaryEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

private theorem six_subset {sk rs wk : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk)
    (region : KRKSixGlobal.Region sk rs wk) (safe : SafeRook sk rs wk)
    (live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t) : KRKTenGlobal.Region sk rs wk := by
  have notRook : rs ≠ wk := by
    intro equal
    rw [equal] at safe
    dsimp [SafeRook,dInf,absDiff] at safe far
    omega
  let q := krkPos .white sk rs wk .black
  have material : IsKRK q .white sk rs wk := ⟨apart,ne_of_dInf_pos (by omega),notRook,rfl⟩
  have six := (KRKSixGlobal.kernel_six_iff material rfl far).mpr (Or.inr ⟨region,safe,live⟩)
  have ten := (KRKTenGlobal.kernel_ten_iff material rfl far).mp (mateWithin_mono six (by decide))
  rcases ten with terminal | result
  · have mate := (KRKMateGeometry.kernel_mate_iff material rfl far).mpr terminal
    obtain ⟨t,guard⟩ := live
    exact False.elim (mate.2 ⟨_,⟨_,KRKCornerWeakBand.guard_legal material rfl guard,rfl⟩⟩)
  · exact result

theorem low_second : KRKTenGlobal.Region (3,2) (4,1) (2,0) := by
  have region : KRKSevenSecond.RookRegion ((4 : Fin 8),1) .east := Or.inr ⟨rfl,by decide⟩
  have props := KRKSevenSecond.properties region
  exact six_subset props.1 props.2.1
    (KRKSevenSecond.global_region_iff.mpr (KRKSevenSecond.shape_iff.mpr ⟨.east,rfl,region⟩))
    props.2.2.2 props.2.2.1

theorem protected_second : KRKTenGlobal.Region (3,2) (1,2) (2,0) := by
  have region : KRKSevenSecond.RookRegion ((1 : Fin 8),2) .east := Or.inl ⟨rfl,by decide⟩
  have props := KRKSevenSecond.properties region
  exact six_subset props.1 props.2.1
    (KRKSevenSecond.global_region_iff.mpr (KRKSevenSecond.shape_iff.mpr ⟨.east,rfl,region⟩))
    props.2.2.2 props.2.2.1

theorem protected_near : KRKTenGlobal.Region (3,2) (1,2) (1,0) := by
  have region : KRKSevenNear.RookRegion ((1 : Fin 8),2) .high := Or.inl ⟨rfl,by decide⟩
  have props := KRKSevenNear.slot_properties (i := .high) (by intro h; cases h) region
  exact six_subset props.1 (by decide)
    (KRKSevenNear.global_region_iff.mpr (KRKSevenNear.shape_iff.mpr ⟨.high,rfl,region⟩))
    props.2.2 props.2.1

theorem protected_clear : KRKTwelveGeometry.Clear ((3 : Fin 8),2) (2,1) (1,1) := by
  refine ⟨Or.inr (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
        t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have bottom : ∀ {j : Fin 8}, j = 0 ∨ j = 1 ∨ j = 2 → KRKElevenGeometry.Clear (3,2) (2,1) (j,0) := by
      intro j edge
      apply KRKElevenGeometry.rook_step_clear (nr := ((2 : Fin 8),3))
      · rcases edge with rfl | rfl | rfl <;> dsimp [RookSees,RookLine,OnSeg] <;> decide
      · decide
      · simp
      · rcases edge with rfl | rfl | rfl
        · exact KRKTwelveInnerOuter.high_corner_ten
        · exact KRKTwelveNearNewEntries.high_near_ten
        · exact KRKTwelveInnerOuter.high_second_ten
    have west : KRKElevenGeometry.Clear (3,2) (2,1) (0,2) := by
      have source : KRKElevenGeometry.Clear (2,3) (1,2) (2,0) :=
        KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by decide) (by decide) protected_second
      have mapped := KRKElevenGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide)
        (by decide) (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide) source
      simpa only [Frame.ofSym,symSwap] using mapped
    rcases targets with rfl | rfl | rfl | rfl | rfl
    · exact bottom (Or.inl rfl)
    · exact bottom (Or.inr (Or.inl rfl))
    · exact bottom (Or.inr (Or.inr rfl))
    · exact west
    · exact (KRKElevenNearStrip.clear_iff (by decide) (by decide)).mpr
        (Or.inr ⟨.side,rfl,Or.inl (Or.inr (Or.inl rfl))⟩)

end EndgameChess.Rules.KRKTwelveInnerBoundaryEntries
