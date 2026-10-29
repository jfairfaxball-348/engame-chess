import EndgameChess.Rules.KRKTwelveCentralStrip

namespace EndgameChess.Rules.KRKElevenEdgeBoundary
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem inner_file_bound {sk rs : Square} (nine : KRKNineInner.Nine sk rs) : sk.1.val ≤ 4 := by
  rcases nine with (⟨i,distance,_,_⟩ | ⟨i,distance,_,_⟩) | (⟨i,equal,_⟩ | ⟨i,equal,_⟩)
  all_goals cases i <;> dsimp [KRKNineInner.king,symSwap,dInf,absDiff] at * <;>
    simp only [square_eq_iff,Fin.ext_iff] at * <;> omega

theorem near_rank_bound {sk rs : Square} (nine : KRKNineNearStrip.Nine sk rs) : sk.2.val ≤ 2 := by
  dsimp [KRKNineNearStrip.Nine,dInf,absDiff] at nine
  simp only [square_eq_iff,Fin.ext_iff] at nine
  dsimp at nine
  omega

private theorem second_file_bound {sk rs : Square} (seven : KRKSevenSecond.Seven sk rs) : sk.1.val ≤ 4 := by
  rcases seven with ⟨i,_,distance⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenSecond.king,dInf,absDiff] at distance <;> omega
  · have x := congrArg (fun s : Square => s.1.val) equal
    cases i <;> dsimp [KRKSevenSecond.king] at x <;> omega

private theorem near_file_bound {sk rs : Square} (seven : KRKSevenNear.Seven sk rs) : sk.1.val ≤ 4 := by
  rcases seven with ⟨i,_,distance,_,_⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenNear.king,dInf,absDiff] at distance <;> omega
  · have x := congrArg (fun s : Square => s.1.val) equal
    cases i <;> dsimp [KRKSevenNear.king] at x <;> omega

private theorem covered_of_no_test {sk rs wk : Square} {i : KRKEightEdge.Reply}
    (region : KRKEightEdge.Region sk rs wk) (distance : dInf wk (KRKEightEdge.destination wk i) = 1)
    (noTest : ¬KRKEightEdge.SevenTest sk rs (KRKEightEdge.destination wk i)) :
    Covered sk rs (KRKEightEdge.destination wk i) := by
  let t := KRKEightEdge.destination wk i
  change dInf wk t = 1 at distance
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have notRook : t ≠ rs := by
    intro equal
    have safe := region.1
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have guard : KRKCornerWeakBand.Guard sk rs wk t :=
    ⟨distance,notRook,by omega,fun seen => line seen.1⟩
  exact False.elim (noTest (region.2.2 i guard))

theorem second_five_two_not_eight {rs : Square} :
    ¬KRKEightEdge.Region ((5 : Fin 8),2) rs (2,0) := by
  intro region
  have a := covered_box (covered_of_no_test (i := .northWest) region (by decide) (by
    simp only [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl]
    simp [KRKSevenInner.Seven,KRKSevenInner.HorizontalRook,dInf,absDiff,symSwap] <;> omega))
  have b := covered_box (covered_of_no_test (i := .north) region (by decide) (by
    simp [KRKEightEdge.SevenTest,KRKEightEdge.destination]))
  dsimp [KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl] at a b
  have rank : rs.2.val = 1 := by omega
  have file : rs.1.val = 1 := by
    by_cases file : rs.1.val = 1
    · exact file
    · have guard : KRKCornerWeakBand.Guard ((5 : Fin 8),2) rs (2,0) (1,0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rank]
        simp <;> omega
      have near : KRKSevenNear.Seven ((5 : Fin 8),2) rs := by
        have test := region.2.2 .west guard
        simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl] using test
      have bound := near_file_bound near
      contradiction
  have equal : rs = ((1 : Fin 8),1) := Prod.ext (Fin.ext file) (Fin.ext rank)
  rw [equal] at region
  obtain ⟨i,guard⟩ := region.2.1
  have test := region.2.2 i guard
  cases i <;> dsimp [KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right,show ((3 : Fin 8).val) = 3 from rfl] at guard test
  · have attacked := guard.2.2.2
    exact attacked (by dsimp [RookSees,RookLine,OnSeg]; decide)
  · have five : KRKFiveMiddle.BottomFive ((5 : Fin 8),2) ((1 : Fin 8),1) (3,0) := by
      simpa [KRKEightEdge.SevenTest] using test
    have noFive : ¬KRKFiveMiddle.BottomFive ((5 : Fin 8),2) ((1 : Fin 8),1) (3,0) := by
      dsimp [KRKFiveMiddle.BottomFive,KRKFiveMiddle.Five,KRKFiveMiddle.KingEntries,
        KRKFiveMiddle.RookEntries,KRKCanonicalSlots.left,KRKCanonicalSlots.right,dInf,absDiff]
      decide
    exact noFive five
  · exact guard.2.1 rfl
  all_goals
    have attacked := guard.2.2.2
    apply attacked
    dsimp [RookSees,RookLine,OnSeg]
    decide

private theorem near_low_rook_king {sk rs : Square} (sx : 4 ≤ sk.1.val)
    (rx : 4 ≤ rs.1.val) (ry : rs.2.val = 1) (seven : KRKSevenNear.Seven sk rs) :
    sk.1.val = 4 ∧ sk.2.val ≤ 1 := by
  rcases seven with ⟨i,shape,distance,_,_⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenNear.king,KRKSevenNear.RookRegion,KRKSevenNear.LowRegion,
      KRKSevenNear.SideRegion,dInf,absDiff] at shape distance <;> omega
  · have file := congrArg (fun t : Square => t.1.val) equal
    cases i <;> dsimp [KRKSevenNear.king] at file <;> omega

theorem second_upper_low_rook {sk rs : Square} (apart : sk ≠ rs) (sx : 4 ≤ sk.1.val)
    (rx : 4 ≤ rs.1.val) (ry : rs.2.val = 1) (region : KRKEightEdge.Region sk rs (2,0)) :
    sk.1.val = 4 ∧ sk.2.val = 0 := by
  have guard : KRKCornerWeakBand.Guard sk rs (2,0) (1,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
    simp <;> omega
  have near : KRKSevenNear.Seven sk rs := by
    have test := region.2.2 .west guard
    simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl] using test
  have shape := near_low_rook_king sx rx ry near
  by_cases zero : sk.2.val = 0
  · exact ⟨shape.1,zero⟩
  have one : sk.2.val = 1 := by omega
  have right : 5 ≤ rs.1.val := by
    simp only [ne_iff_coords] at apart
    omega
  have inward : KRKCornerWeakBand.Guard sk rs (2,0) (1,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,one,ry,shape.1]
    simp <;> omega
  have inner : KRKSevenInner.Seven sk rs := by
    have test := region.2.2 .northWest inward
    simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl] using test
  dsimp [KRKSevenInner.Seven,KRKSevenInner.HorizontalRook,dInf,absDiff] at inner
  simp only [square_eq_iff,Fin.ext_iff] at inner
  dsimp [symSwap] at inner
  omega

theorem second_five_two_not_nine {rs : Square} (rx : 4 ≤ rs.1.val) (ry : rs.2.val = 1) :
    ¬KRKNineGeometry.Clear ((5 : Fin 8),2) rs (2,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),2) (KRKNineSlots.point i) = 1 at distance
    change KRKNineSlots.point i ≠ rs at apart
    change KRKEightEdge.Region (KRKNineSlots.point i) rs (2,0) at region
    have high : 4 ≤ (KRKNineSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have shape := second_upper_low_rook apart high rx ry region
    dsimp [dInf,absDiff] at distance
    omega
  · change KRKEightEdge.Region ((5 : Fin 8),2) _ (2,0) at region
    exact second_five_two_not_eight region

private theorem nine_two_one_forbidden {sk rs wk : Square} (apart : sk ≠ rs)
    (high : 4 ≤ sk.1.val) (guard : KRKCornerWeakBand.Guard sk rs wk (2,1)) :
    ¬KRKNineGeometry.Clear sk rs (2,1) := by
  intro clear
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKNineGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2 clear
  have condition := (KRKNineNearStrip.clear_iff (g.ne_iff.mpr apart) (g.ne_iff.mpr notKing)
    (g.ne_iff.mpr guard.2.1.symm) (by
      change 2 ≤ dInf (g.f sk) (g.f ((2 : Fin 8),1))
      rw [g.distance]; exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mp mapped
  have bound := near_rank_bound condition
  change sk.1.val ≤ 2 at bound
  omega

theorem ten_high_near_cover {sk rs wk : Square} (apart : sk ≠ rs) (high : 4 ≤ sk.1.val)
    (clear : KRKTenGeometry.Clear sk rs wk) (distance : dInf wk (2,1) = 1) : Covered sk rs (2,1) := by
  by_cases king : dInf sk (2,1) ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs (2,1)
  · exact Or.inr line
  have notRook : ((2 : Fin 8),1) ≠ rs := by
    intro equal
    have safe := clear.1
    rcases safe with distant | guarded
    · rw [←equal] at distant
      have back : dInf ((2 : Fin 8),1) wk = 1 := by rwa [dInf_comm]
      omega
    · rw [←equal] at guarded
      omega
  have guard : KRKCornerWeakBand.Guard sk rs wk (2,1) :=
    ⟨distance,notRook,by omega,fun seen => line seen.1⟩
  exact False.elim (nine_two_one_forbidden apart high guard (clear.2.2 _ guard))

theorem middle_ten_high_rook_rank {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 5)
    (clear : KRKTenGeometry.Clear sk rs (3,0)) : rs.2.val = 1 := by
  have a := covered_box (ten_high_near_cover apart (by omega) clear (by decide))
  have b := covered_box (KRKTenSecondCorner.bad_neighbour_covered apart clear (t := (3,1)) (by decide)
    (Or.inr (Or.inr ⟨Or.inl rfl,by decide,by decide⟩)))
  dsimp at a b
  omega

theorem middle_five_two_not_eleven {rs : Square} (rx : 4 ≤ rs.1.val) (ry : rs.2.val = 2) :
    ¬KRKElevenGeometry.Clear ((5 : Fin 8),2) rs (3,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),2) (KRKElevenSlots.point i) = 1 at distance
    change KRKElevenSlots.point i ≠ rs at apart
    change KRKTenEdge.Region (KRKElevenSlots.point i) rs (3,0) at region
    have high : 4 ≤ (KRKElevenSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have ten := (KRKTenEdge.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) apart).mpr region
    have covered := covered_box (ten_high_near_cover apart high ten (by decide))
    dsimp at covered
    omega
  · let nr := a.target rs v
    change RookSees rs nr ((5 : Fin 8),2) (3,0) at sees
    change nr ≠ ((5 : Fin 8),2) at notKing
    change KRKTenEdge.Region ((5 : Fin 8),2) nr (3,0) at region
    have ten := (KRKTenEdge.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) notKing.symm).mpr region
    have rank := middle_ten_high_rook_rank notKing.symm rfl ten
    have line := sees.1
    have file : nr.1.val = rs.1.val := by dsimp [RookLine] at line; omega
    have guard : KRKCornerWeakBand.Guard ((5 : Fin 8),2) nr (3,0) (2,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rank,file]
      simp <;> omega
    exact second_five_two_not_nine (by omega) rank (ten.2.2 _ guard)

theorem middle_five_one_not_eleven {rs : Square} (rx : 5 ≤ rs.1.val) (ry : rs.2.val = 2) :
    ¬KRKElevenGeometry.Clear ((5 : Fin 8),1) rs (3,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),1) (KRKElevenSlots.point i) = 1 at distance
    change KRKElevenSlots.point i ≠ rs at apart
    change KRKTenEdge.Region (KRKElevenSlots.point i) rs (3,0) at region
    have high : 4 ≤ (KRKElevenSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have ten := (KRKTenEdge.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) apart).mpr region
    have covered := covered_box (ten_high_near_cover apart high ten (by decide))
    dsimp at covered
    omega
  · let nr := a.target rs v
    change RookSees rs nr ((5 : Fin 8),1) (3,0) at sees
    change nr ≠ ((5 : Fin 8),1) at notKing
    change KRKTenEdge.Region ((5 : Fin 8),1) nr (3,0) at region
    have ten := (KRKTenEdge.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) notKing.symm).mpr region
    have rank := middle_ten_high_rook_rank notKing.symm rfl ten
    have line := sees.1
    have file : nr.1.val = rs.1.val := by dsimp [RookLine] at line; omega
    have high : 6 ≤ nr.1.val := by simp only [ne_iff_coords] at notKing; dsimp at notKing; omega
    have guard : KRKCornerWeakBand.Guard ((5 : Fin 8),1) nr (3,0) (3,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rank]
      simp <;> omega
    have nine := ten.2.2 _ guard
    let q := krkPos .white (5,1) nr (3,1) .white
    have sourceNotWeak : nr ≠ ((3 : Fin 8),1) := by simp only [ne_iff_coords]; dsimp; omega
    have material : IsKRK q .white (5,1) nr (3,1) := ⟨notKing.symm,by decide,sourceNotWeak,rfl⟩
    have win := KRKNineGeometry.sufficient material rfl guard.2.2.1 guard.2.2.2 nine
    exact KRKEightCentralStripHolding.strong_no_ten material rfl
      (Or.inr ⟨Or.inl rfl,by decide,by decide⟩) (mateWithin_mono win (by decide))

theorem middle_five_zero_not_eight {rs : Square} :
    ¬KRKEightEdge.Region ((5 : Fin 8),0) rs (3,0) := by
  intro region
  obtain ⟨i,guard⟩ := region.2.1
  have test := region.2.2 i guard
  cases i with
  | west =>
    have seven : KRKSevenSecond.Seven ((5 : Fin 8),0) rs := by
      simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl] using test
    have bound := second_file_bound seven
    contradiction
  | east =>
    have far := guard.2.2.1
    change 2 ≤ dInf ((5 : Fin 8),0) (4,0) at far
    contradiction
  | northWest => simp [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl] at test
  | north => simp [KRKEightEdge.SevenTest,KRKEightEdge.destination] at test
  | northEast => simp [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.right,show ((3 : Fin 8).val) = 3 from rfl] at test

theorem middle_five_zero_not_nine {rs : Square} (rx : 4 ≤ rs.1.val) (ry : rs.2.val = 1) :
    ¬KRKNineGeometry.Clear ((5 : Fin 8),0) rs (3,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),0) (KRKNineSlots.point i) = 1 at distance
    change 2 ≤ dInf (KRKNineSlots.point i) (3,0) at far
    change KRKEightEdge.Region (KRKNineSlots.point i) rs (3,0) at region
    have high : 5 ≤ (KRKNineSlots.point i).1.val := by dsimp [dInf,absDiff] at distance far; omega
    have guard : KRKCornerWeakBand.Guard (KRKNineSlots.point i) rs (3,0) (2,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
      simp <;> omega
    have seven : KRKSevenSecond.Seven (KRKNineSlots.point i) rs := by
      have test := region.2.2 .west guard
      simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,show ((3 : Fin 8).val) = 3 from rfl] using test
    have bound := second_file_bound seven
    omega
  · change KRKEightEdge.Region ((5 : Fin 8),0) _ (3,0) at region
    exact middle_five_zero_not_eight region

private theorem ten_high_inner_cover {sk rs wk : Square} (apart : sk ≠ rs) (sx : sk.1.val = 5)
    (clear : KRKTenGeometry.Clear sk rs wk) (distance : dInf wk (1,1) = 1) : Covered sk rs (1,1) := by
  by_cases king : dInf sk (1,1) ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs (1,1)
  · exact Or.inr line
  have notRook : ((1 : Fin 8),1) ≠ rs := by
    intro equal
    have safe := clear.1
    rcases safe with distant | guarded
    · rw [←equal] at distant
      have back : dInf ((1 : Fin 8),1) wk = 1 := by rwa [dInf_comm]
      omega
    · rw [←equal] at guarded
      omega
  have guard : KRKCornerWeakBand.Guard sk rs wk (1,1) :=
    ⟨distance,notRook,by omega,fun seen => line seen.1⟩
  have condition := (KRKNineInner.clear_iff apart (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
    guard.2.1.symm guard.2.2.1 guard.2.2.2).mp (clear.2.2 _ guard)
  have bound := inner_file_bound condition
  omega

theorem second_ten_high_rook_rank {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 5)
    (clear : KRKTenGeometry.Clear sk rs (2,0)) : rs.2.val = 1 := by
  have a := covered_box (ten_high_near_cover apart (by omega) clear (by decide))
  have b := covered_box (ten_high_inner_cover apart sx clear (by decide))
  dsimp at a b
  omega

theorem second_five_zero_not_eleven {rs : Square} (rx : 4 ≤ rs.1.val) (ry : rs.2.val = 2) :
    ¬KRKElevenGeometry.Clear ((5 : Fin 8),0) rs (2,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),0) (KRKElevenSlots.point i) = 1 at distance
    change KRKElevenSlots.point i ≠ rs at apart
    change KRKTenEdge.Region (KRKElevenSlots.point i) rs (2,0) at region
    have high : 4 ≤ (KRKElevenSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have ten := (KRKTenEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide) apart).mpr region
    have covered := covered_box (ten_high_near_cover apart high ten (by decide))
    dsimp at covered
    omega
  · let nr := a.target rs v
    change RookSees rs nr ((5 : Fin 8),0) (2,0) at sees
    change nr ≠ ((5 : Fin 8),0) at notKing
    change KRKTenEdge.Region ((5 : Fin 8),0) nr (2,0) at region
    have ten := (KRKTenEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide) notKing.symm).mpr region
    have rank := second_ten_high_rook_rank notKing.symm rfl ten
    have line := sees.1
    have file : nr.1.val = rs.1.val := by dsimp [RookLine] at line; omega
    have guard : KRKCornerWeakBand.Guard ((5 : Fin 8),0) nr (2,0) (3,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rank,file]
      simp <;> omega
    exact middle_five_zero_not_nine (by omega) rank (ten.2.2 _ guard)

theorem near_ten_high_rook_rank {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 5)
    (clear : KRKTenGeometry.Clear sk rs (1,0)) : rs.2.val = 1 := by
  have a := covered_box (ten_high_near_cover apart (by omega) clear (by decide))
  have b := covered_box (ten_high_inner_cover apart sx clear (by decide))
  dsimp at a b
  omega

theorem near_five_one_not_eleven {rs : Square} (rx : 5 ≤ rs.1.val) (ry : rs.2.val = 2) :
    ¬KRKElevenGeometry.Clear ((5 : Fin 8),1) rs (1,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),1) (KRKElevenSlots.point i) = 1 at distance
    change KRKElevenSlots.point i ≠ rs at apart
    change KRKTenEdge.Region (KRKElevenSlots.point i) rs (1,0) at region
    have high : 4 ≤ (KRKElevenSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have ten := (KRKTenEdge.clear_iff (wk := ((1 : Fin 8),0)) rfl (by decide) apart).mpr region
    have covered := covered_box (ten_high_near_cover apart high ten (by decide))
    dsimp at covered
    omega
  · let nr := a.target rs v
    change RookSees rs nr ((5 : Fin 8),1) (1,0) at sees
    change nr ≠ ((5 : Fin 8),1) at notKing
    change KRKTenEdge.Region ((5 : Fin 8),1) nr (1,0) at region
    have ten := (KRKTenEdge.clear_iff (wk := ((1 : Fin 8),0)) rfl (by decide) notKing.symm).mpr region
    have rank := near_ten_high_rook_rank notKing.symm rfl ten
    have line := sees.1
    have file : nr.1.val = rs.1.val := by dsimp [RookLine] at line; omega
    have high : 6 ≤ nr.1.val := by simp only [ne_iff_coords] at notKing; dsimp at notKing; omega
    have guard : KRKCornerWeakBand.Guard ((5 : Fin 8),1) nr (1,0) (1,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rank]
      simp <;> omega
    have condition := (KRKNineInner.clear_iff notKing.symm (by decide) guard.2.1.symm
      guard.2.2.1 guard.2.2.2).mp (ten.2.2 _ guard)
    have bound := inner_file_bound condition
    contradiction

private theorem four_low_row_no_five {sk rs : Square} (sx : sk.1.val ≤ 2) (ry : rs.2.val = 1) :
    ¬KRKFiveMiddle.BottomFive sk rs (4,0) := by
  change ¬KRKFiveMiddle.Five (symX.f sk) (symX.f rs) ((3 : Fin 8),0)
  dsimp [KRKFiveMiddle.Five,KRKFiveMiddle.KingEntries,KRKFiveMiddle.RookEntries,
    KRKCanonicalSlots.left,KRKCanonicalSlots.right,symX,dInf,absDiff]
  simp only [square_eq_iff,Fin.ext_iff,show ((3 : Fin 8).val) = 3 from rfl]
  dsimp
  omega

private theorem four_high_rook_no_five {sk rs : Square} (sx : sk.1.val ≤ 3)
    (rx : 6 ≤ rs.1.val) (ry : rs.2.val = 1) : ¬KRKFiveMiddle.BottomFive sk rs (4,0) := by
  change ¬KRKFiveMiddle.Five (symX.f sk) (symX.f rs) ((3 : Fin 8),0)
  dsimp [KRKFiveMiddle.Five,KRKFiveMiddle.KingEntries,KRKFiveMiddle.RookEntries,
    KRKCanonicalSlots.left,KRKCanonicalSlots.right,symX,dInf,absDiff]
  simp only [square_eq_iff,Fin.ext_iff,show ((3 : Fin 8).val) = 3 from rfl]
  dsimp
  omega

theorem middle_left_low_row_not_eight {sk rs : Square} (sx : sk.1.val ≤ 2) (ry : rs.2.val = 1) :
    ¬KRKEightEdge.Region sk rs (3,0) := by
  intro region
  have notFour : rs.1.val ≠ 4 := by
    have safe := region.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (3,0) (4,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
    simp <;> omega
  have five : KRKFiveMiddle.BottomFive sk rs (4,0) := by
    have test := region.2.2 .east guard
    simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.right,
      show ((3 : Fin 8).val) = 3 from rfl] using test
  exact four_low_row_no_five sx ry five

theorem middle_one_three_not_eight {rs : Square} :
    ¬KRKEightEdge.Region ((1 : Fin 8),3) rs (3,0) := by
  intro region
  have a := covered_box (covered_of_no_test (i := .northWest) region (by decide) (by
    simp [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.left,
      show ((3 : Fin 8).val) = 3 from rfl]))
  have b := covered_box (covered_of_no_test (i := .northEast) region (by decide) (by
    simp [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.right,
      show ((3 : Fin 8).val) = 3 from rfl]))
  dsimp [KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right] at a b
  have rank : rs.2.val = 1 := by omega
  exact middle_left_low_row_not_eight (by decide) rank region

theorem middle_left_high_rook_not_eight {sk rs : Square} (sx : sk.1.val ≤ 3)
    (rx : 6 ≤ rs.1.val) (ry : rs.2.val = 1) (far : 2 ≤ dInf sk (3,0)) :
    ¬KRKEightEdge.Region sk rs (3,0) := by
  intro region
  have guard : KRKCornerWeakBand.Guard sk rs (3,0) (4,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
    dsimp [dInf,absDiff] at far
    simp <;> omega
  have five : KRKFiveMiddle.BottomFive sk rs (4,0) := by
    have test := region.2.2 .east guard
    simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.right,
      show ((3 : Fin 8).val) = 3 from rfl] using test
  exact four_high_rook_no_five sx rx ry five

theorem middle_left_high_rook_not_nine {sk rs : Square} (sx : sk.1.val ≤ 2)
    (rx : 6 ≤ rs.1.val) (ry : rs.2.val = 1) : ¬KRKNineGeometry.Clear sk rs (3,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf sk (KRKNineSlots.point i) = 1 at distance
    change 2 ≤ dInf (KRKNineSlots.point i) (3,0) at far
    change KRKEightEdge.Region (KRKNineSlots.point i) rs (3,0) at region
    have file : (KRKNineSlots.point i).1.val ≤ 3 := by dsimp [dInf,absDiff] at distance; omega
    exact middle_left_high_rook_not_eight file rx ry far region
  · let nr := a.target rs v
    change RookSees rs nr sk (3,0) at sees
    change KRKEightEdge.Region sk nr (3,0) at region
    have covered := covered_box (covered_of_no_test (i := .northEast) region (by decide) (by
      simp [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.right,
        show ((3 : Fin 8).val) = 3 from rfl]))
    dsimp [KRKEightEdge.destination,KRKEightEdge.right] at covered
    have line := sees.1
    have rank : nr.2.val = 1 := by dsimp [RookLine] at line; omega
    exact middle_left_low_row_not_eight sx rank region

theorem middle_one_three_low_row_not_nine {rs : Square} (ry : rs.2.val = 1) :
    ¬KRKNineGeometry.Clear ((1 : Fin 8),3) rs (3,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((1 : Fin 8),3) (KRKNineSlots.point i) = 1 at distance
    change KRKEightEdge.Region (KRKNineSlots.point i) rs (3,0) at region
    have file : (KRKNineSlots.point i).1.val ≤ 2 := by dsimp [dInf,absDiff] at distance; omega
    exact middle_left_low_row_not_eight file ry region
  · change KRKEightEdge.Region ((1 : Fin 8),3) _ (3,0) at region
    exact middle_one_three_not_eight region

theorem second_one_three_high_rook_not_eleven {rs : Square} (rx : 6 ≤ rs.1.val) (ry : rs.2.val = 1) :
    ¬KRKElevenGeometry.Clear ((1 : Fin 8),3) rs (2,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((1 : Fin 8),3) (KRKElevenSlots.point i) = 1 at distance
    change KRKElevenSlots.point i ≠ rs at apart
    change KRKTenEdge.Region (KRKElevenSlots.point i) rs (2,0) at region
    have file : (KRKElevenSlots.point i).1.val ≤ 2 := by dsimp [dInf,absDiff] at distance; omega
    have height : 2 ≤ (KRKElevenSlots.point i).2.val := by dsimp [dInf,absDiff] at distance; omega
    have ten := (KRKTenEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide) apart).mpr region
    have guard : KRKCornerWeakBand.Guard (KRKElevenSlots.point i) rs (2,0) (3,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
      simp <;> omega
    exact middle_left_high_rook_not_nine file rx ry (ten.2.2 _ guard)
  · let nr := a.target rs v
    change RookSees rs nr ((1 : Fin 8),3) (2,0) at sees
    change nr ≠ ((1 : Fin 8),3) at notKing
    change KRKTenEdge.Region ((1 : Fin 8),3) nr (2,0) at region
    have ten := (KRKTenEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide) notKing.symm).mpr region
    have covered := covered_box (KRKTenSecondCorner.bad_neighbour_covered notKing.symm ten (t := (3,1)) (by decide)
      (Or.inr (Or.inr ⟨Or.inl rfl,by decide,by decide⟩)))
    dsimp at covered
    have line := sees.1
    have rank : nr.2.val = 1 := by dsimp [RookLine] at line; omega
    have notThree : nr.1.val ≠ 3 := by
      have safe := ten.1
      dsimp [SafeRook,dInf,absDiff] at safe
      omega
    have guard : KRKCornerWeakBand.Guard ((1 : Fin 8),3) nr (2,0) (3,0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rank]
      simp <;> omega
    exact middle_one_three_low_row_not_nine rank (ten.2.2 _ guard)

end EndgameChess.Rules.KRKElevenEdgeBoundary
