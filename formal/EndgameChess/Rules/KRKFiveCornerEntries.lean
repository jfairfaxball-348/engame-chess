import EndgameChess.Rules.KRKSixSecond

namespace EndgameChess.Rules.KRKFiveCornerEntries
open EndgameChess.KK KRKNativeFrame KRKFiveGeometry
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

private theorem val0 : ((0 : Fin 8).val) = 0 := rfl
private theorem val1 : ((1 : Fin 8).val) = 1 := rfl
private theorem val2 : ((2 : Fin 8).val) = 2 := rfl
private theorem val3 : ((3 : Fin 8).val) = 3 := rfl
private theorem val4 : ((4 : Fin 8).val) = 4 := rfl

theorem slot22_properties {rs : Square} (region : KRKFourSlots.Region (0,0) rs .c22) :
    ((2 : Fin 8),2) ≠ rs ∧ Live (2,2) rs (0,0) ∧ SafeRook (2,2) rs (0,0) := by
  have apart : ((2 : Fin 8),2) ≠ rs := by
    simp only [KRKFourSlots.Region] at region
    rw [ne_iff_coords]
    dsimp only
    simp only [val0,val1,val2,val3] at *
    simp_all [val0,val1,val2,val3,val4] <;> omega
  have safe : SafeRook (2,2) rs (0,0) := by
    apply Or.inl
    simp only [KRKFourSlots.Region] at region
    simp only [dInf,absDiff,val0,val2]
    simp_all [val0,val1,val2,val3,val4] <;> omega
  refine ⟨apart,?_,safe⟩
  by_cases low : rs.2.val = 1 ∨ rs.1.val = 0
  · refine ⟨((1 : Fin 8),0),?_⟩
    simp only [KRKFourSlots.Region] at region
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,
      val0,val1,val2,val3]
    simp_all [val0,val1,val2,val3,val4] <;> omega
  · refine ⟨((0 : Fin 8),1),?_⟩
    simp only [KRKFourSlots.Region] at region
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,
      val0,val1,val2,val3]
    simp_all [val0,val1,val2,val3,val4] <;> omega

theorem corner22_reachable {rs : Square} (apart : ((2 : Fin 8),2) ≠ rs)
    (apartWeak : rs ≠ ((0 : Fin 8),0))
    (notCheck : ¬RookSees rs (0,0) (2,2) (0,0)) :
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
      RookSees rs (a.target rs v) (2,2) (0,0) ∧
      KRKFourSlots.Region (0,0) (a.target rs v) .c22 := by
  have positive : 1 ≤ rs.1.val ∧ 1 ≤ rs.2.val := by
    simp only [ne_iff_coords,val0] at apartWeak
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,val0,val2] at notCheck
    omega
  by_cases x1 : rs.1.val = 1
  · by_cases y2 : rs.2.val = 2
    · refine ⟨.rank,0,?_,?_⟩ <;>
        simp only [KRKCornerSlotBarriers.Axis.target,KRKFourSlots.Region,RookSees,RookLine,OnSeg,ne_iff_coords,
          x1,y2,val0,val1,val2,val3] <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega
    · refine ⟨.file,2,?_,?_⟩ <;>
        simp only [KRKCornerSlotBarriers.Axis.target,KRKFourSlots.Region,RookSees,RookLine,OnSeg,ne_iff_coords,
          x1,val0,val1,val2,val3] <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega
  by_cases x2 : rs.1.val = 2
  · have notTwo : rs.2.val ≠ 2 := by
      simp only [ne_iff_coords,val2] at apart
      simp_all [val0,val1,val2,val3,val4] <;> omega
    by_cases y1 : rs.2.val = 1
    · refine ⟨.file,0,?_,?_⟩ <;>
        simp only [KRKCornerSlotBarriers.Axis.target,KRKFourSlots.Region,RookSees,RookLine,OnSeg,ne_iff_coords,
          x2,y1,val0,val1,val2,val3] <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega
    · refine ⟨.rank,0,?_,?_⟩ <;>
        simp only [KRKCornerSlotBarriers.Axis.target,KRKFourSlots.Region,RookSees,RookLine,OnSeg,ne_iff_coords,
          x2,val0,val1,val2,val3] <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega
  · have high : 3 ≤ rs.1.val := by omega
    let v : Fin 8 := if rs.2.val = 3 then 4 else 3
    have height : 3 ≤ v.val ∧ v.val ≠ rs.2.val := by dsimp [v]; split <;> simp_all <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega
    refine ⟨.file,v,?_,?_⟩ <;>
      simp only [KRKCornerSlotBarriers.Axis.target,KRKFourSlots.Region,RookSees,RookLine,OnSeg,ne_iff_coords,
        val0,val1,val2,val3] <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega

/-- At the canonical corner, the diagonal king (2,2) can always enter a
live four-ply corner region in one legal rook move from a nonchecking root. -/
theorem corner22_five {rs : Square} (apart : ((2 : Fin 8),2) ≠ rs)
    (apartWeak : rs ≠ ((0 : Fin 8),0))
    (notCheck : ¬RookSees rs (0,0) (2,2) (0,0)) : Clear (2,2) rs (0,0) := by
  obtain ⟨a,v,sees,region⟩ := corner22_reachable apart apartWeak notCheck
  obtain ⟨notKing,live,safe⟩ := slot22_properties region
  have notWeak : a.target rs v ≠ ((0 : Fin 8),0) := by
    simp only [KRKFourSlots.Region] at region
    rw [ne_iff_coords]
    simp only [val0]
    simp_all [val0,val1,val2,val3,val4] <;> omega
  refine Or.inr ⟨by decide,Or.inr ?_⟩
  simp only [RookRays,KRKFiveMiddle.normalize_f (wk := ((0 : Fin 8),0)) rfl (by decide),
    KRKFiveMiddle.normalize_r (wk := ((0 : Fin 8),0)) rfl (by decide)]
  exact ⟨.c22,rfl,rfl,a,v,sees,notKing.symm,notWeak,region,live,safe⟩

theorem corner22_king_five {sk rs : Square} (distance : dInf sk ((2 : Fin 8),2) = 1)
    (region : KRKFourSlots.Region (0,0) rs .c22) : Clear sk rs (0,0) := by
  obtain ⟨apart,live,safe⟩ := slot22_properties region
  refine Or.inr ⟨by decide,Or.inl ?_⟩
  simp only [KingPoints,KRKFiveMiddle.normalize_f (wk := ((0 : Fin 8),0)) rfl (by decide),
    KRKFiveMiddle.normalize_r (wk := ((0 : Fin 8),0)) rfl (by decide)]
  exact ⟨.c22,rfl,region,distance,apart,by decide,live,safe⟩

/-- Moving the outside king inward can deliberately block its own rook
and preserve a legal defender reply at the corner. -/
theorem low_right_five {sk rs : Square} (sx : sk.1.val = 3) (sy : sk.2.val ≤ 1)
    (ry : rs.2.val = 1) (rx : 3 ≤ rs.1.val) : Clear sk rs (0,0) := by
  refine Or.inr ⟨by decide,Or.inl ?_⟩
  simp only [KingPoints,KRKFiveMiddle.normalize_f (wk := ((0 : Fin 8),0)) rfl (by decide),
    KRKFiveMiddle.normalize_r (wk := ((0 : Fin 8),0)) rfl (by decide)]
  refine ⟨.c21,rfl,by change 1 ≤ rs.1.val; omega,?_,?_,by decide,?_,?_⟩
  · simp only [KRKFourSlots.king,dInf,absDiff,sx,val0,val1,val2,val3]; omega
  · simp only [KRKFourSlots.king,ne_iff_coords,val1,val2]; omega
  · refine ⟨((0 : Fin 8),1),?_⟩
    simp only [KRKFourSlots.king,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,
      ne_iff_coords,ry,val0,val1,val2]
    simp <;> omega
  · apply Or.inl
    simp only [dInf,absDiff,ry,val0]; omega

theorem side_right_five {sk rs : Square} (sx : sk.1.val = 3)
    (sy : sk.2.val ≤ 2) (rx : rs.1.val = 1) (ry : 2 ≤ rs.2.val) :
    Clear sk rs (0,0) := by
  by_cases two : rs.2.val = 2
  · by_cases low : sk.2.val = 0
    · refine Or.inr ⟨by decide,Or.inl ?_⟩
      simp only [KingPoints,KRKFiveMiddle.normalize_f (wk := ((0 : Fin 8),0)) rfl (by decide),
        KRKFiveMiddle.normalize_r (wk := ((0 : Fin 8),0)) rfl (by decide)]
      refine ⟨.c21,rfl,by change 1 ≤ rs.1.val; omega,?_,?_,by decide,?_,?_⟩
      · simp [KRKFourSlots.king,dInf,absDiff,sx,low,val2]
      · simp only [KRKFourSlots.king,ne_iff_coords,rx,two,val1,val2]; omega
      · refine ⟨((0 : Fin 8),1),?_⟩
        simp [KRKFourSlots.king,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,
          ne_iff_coords,rx,two,val0,val1,val2]
      · apply Or.inl
        simp only [dInf,absDiff,two,val0]; omega
    apply corner22_king_five
    · simp only [dInf,absDiff,sx,val2]; omega
    · change (3 ≤ rs.1.val ∧ 3 ≤ rs.2.val) ∨ (rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
        (rs.2.val = 0 ∧ 2 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ rs.2.val = 2) ∨
        (rs.1.val = 2 ∧ rs.2.val = 1)
      omega
  · let a : Fin 3 := ⟨sk.2.val,by omega⟩
    have equal : sk = KRKFourSlots.king (0,0) (.cRight a) := by
      rw [square_eq_iff]
      dsimp [KRKFourSlots.king,KRKFourSlots.small,a]
      exact ⟨sx,rfl⟩
    refine Or.inr ⟨by decide,Or.inr ?_⟩
    simp only [RookRays,KRKFiveMiddle.normalize_f (wk := ((0 : Fin 8),0)) rfl (by decide),
      KRKFiveMiddle.normalize_r (wk := ((0 : Fin 8),0)) rfl (by decide)]
    refine ⟨.cRight a,rfl,equal,.file,2,?_,?_,?_,?_,?_,?_⟩
    · simp only [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg,ne_iff_coords,rx,sx,val0,val1,val2]
      simp <;> omega
    · simp only [KRKCornerSlotBarriers.Axis.target,ne_iff_coords,rx,sx,val1,val2]; omega
    · simp only [KRKCornerSlotBarriers.Axis.target,ne_iff_coords,rx,val0,val1,val2]; omega
    · change rs.1.val = 1 ∧ ((2 : Fin 8).val) = 2
      exact ⟨rx,rfl⟩
    · refine ⟨((0 : Fin 8),1),?_⟩
      simp only [KRKCornerSlotBarriers.Axis.target,KRKCornerWeakBand.Guard,dInf,absDiff,
        RookSees,RookLine,OnSeg,ne_iff_coords,rx,sx,val0,val1,val2,val3]
      omega
    · apply Or.inl
      simp only [KRKCornerSlotBarriers.Axis.target,dInf,absDiff,rx,val0,val1,val2]; omega

theorem no_capture_square_entry : ¬Clear ((3 : Fin 8),0) ((2 : Fin 8),1) ((0 : Fin 8),0) := by
  intro clear
  simp only [Clear,KingPoints,RookRays,
    KRKFiveMiddle.normalize_f (wk := ((0 : Fin 8),0)) rfl (by decide),
    KRKFiveMiddle.normalize_r (wk := ((0 : Fin 8),0)) rfl (by decide)] at clear
  rcases clear with immediate | ⟨_,points | rays⟩
  · simp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,
      KRKImmediate.fileTarget,RookSees,RookLine,OnSeg,absDiff,val0,val1,val2,val3] at immediate
  · obtain ⟨i,valid,region,distance,apart,_,⟨t,guard⟩,_⟩ := points
    cases i <;>
      dsimp [KRKFourSlots.Valid,KRKFourSlots.Region,KRKFourSlots.king,KRKFourSlots.small] at valid region distance apart guard <;>
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at distance guard apart <;>
      (try dsimp only at *) <;>
      (try simp_all [val0,val1,val2,val3,val4]) <;>
      (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4] at *) <;> omega
  · obtain ⟨i,valid,equal,a,v,sees,_,_,region,_⟩ := rays
    cases i <;>
      dsimp [KRKFourSlots.Valid,KRKFourSlots.Region,KRKFourSlots.king,KRKFourSlots.small] at valid equal region <;>
      simp only [square_eq_iff] at equal <;>
      (try dsimp only at equal) <;>
      (try simp_all [val0,val1,val2,val3,val4])
    all_goals cases a <;>
      dsimp [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg] at sees region <;>
      omega

end EndgameChess.Rules.KRKFiveCornerEntries
