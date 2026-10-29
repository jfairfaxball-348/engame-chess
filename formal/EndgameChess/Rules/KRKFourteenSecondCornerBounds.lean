import EndgameChess.Rules.KRKFourteenSecondCornerEntries

namespace EndgameChess.Rules.KRKFourteenSecondCornerBounds
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private theorem inner_region_iff {sk rs : Square} :
    KRKTwelveGlobal.Region sk rs (1,1) ↔ KRKTwelveInnerExact.Region sk rs := by
  simp [KRKTwelveGlobal.Region,KRKEdgeDepth.depth,KRKTwelveInteriorExact.Region,KRKTwelveInteriorExact.StripRegion,
    KRKEightInteriorExact.stripFrame,Frame.ofSym,symId]

theorem near_four_zero_no_thirteen {k : Fin 8} : ¬KRKThirteenGeometry.Clear (4,k) (0,3) (1,2) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((4,k) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) (0,3) (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp [dInf,absDiff] at distance
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((4,k) : Square) _ (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem near_four_two_file_two_no_thirteen {rs : Square} (rx : rs.1.val = 2) (notThree : rs.2.val ≠ 3) : ¬KRKThirteenGeometry.Clear (4,2) rs (1,2) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((4,2) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp [dInf,absDiff] at distance
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((4,2) : Square) _ (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem near_three_four_no_thirteen  : ¬KRKThirteenGeometry.Clear (3,4) (3,3) (1,2) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((3,4) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) (3,3) (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp [dInf,absDiff] at distance
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((3,4) : Square) _ (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem central_four_three_no_thirteen {r : Fin 8} : ¬KRKThirteenGeometry.Clear (4,3) (r,3) (1,3) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((4,3) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) (r,3) (1,3) at region
    have shape := KRKThirteenInteriorBarriers.central_region_iff.mp region
    dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,KRKTwelveCentralExact.Opposition] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp [dInf,absDiff] at distance
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((4,3) : Square) _ (1,3) at region
    have shape := KRKThirteenInteriorBarriers.central_region_iff.mp region
    dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,KRKTwelveCentralExact.Opposition] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem central_three_four_no_thirteen {r : Fin 8} : ¬KRKThirteenGeometry.Clear (3,4) (r,2) (1,3) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((3,4) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) (r,2) (1,3) at region
    have shape := KRKThirteenInteriorBarriers.central_region_iff.mp region
    dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,KRKTwelveCentralExact.Opposition] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp [dInf,absDiff] at distance
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((3,4) : Square) _ (1,3) at region
    have shape := KRKThirteenInteriorBarriers.central_region_iff.mp region
    dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,KRKTwelveCentralExact.Opposition] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem inner_diagonal_no_thirteen  : ¬KRKThirteenGeometry.Clear (4,4) (3,3) (1,1) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((4,4) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) (3,3) (1,1) at region
    have shape := inner_region_iff.mp region
    dsimp [KRKTwelveInnerExact.Region,KRKTwelveInnerExact.Horizontal,KRKTwelveInnerExact.Low,KRKTwelveInnerExact.Side,KRKTwelveInnerExact.High,KRKTwelveInnerExact.Diagonal,KRKTwelveInnerExact.Outer,KRKTwelveInnerExact.UpperFive,KRKTwelveInnerUpperFour.Region,KRKTwelveInnerSide.Region,KRKTwelveInnerHighExact.Region,KRKTwelveInnerDiagonalExact.Region,KRKNineNearStrip.RookCondition,symSwap] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp [dInf,absDiff] at distance
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((4,4) : Square) _ (1,1) at region
    have shape := inner_region_iff.mp region
    dsimp [KRKTwelveInnerExact.Region,KRKTwelveInnerExact.Horizontal,KRKTwelveInnerExact.Low,KRKTwelveInnerExact.Side,KRKTwelveInnerExact.High,KRKTwelveInnerExact.Diagonal,KRKTwelveInnerExact.Outer,KRKTwelveInnerExact.UpperFive,KRKTwelveInnerUpperFour.Region,KRKTwelveInnerSide.Region,KRKTwelveInnerHighExact.Region,KRKTwelveInnerDiagonalExact.Region,KRKNineNearStrip.RookCondition,symSwap] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    (try dsimp at shape)
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

end EndgameChess.Rules.KRKFourteenSecondCornerBounds
