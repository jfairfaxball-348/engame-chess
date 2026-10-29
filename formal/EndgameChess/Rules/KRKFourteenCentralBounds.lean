import EndgameChess.Rules.KRKFourteenCentralUpperEntries

namespace EndgameChess.Rules.KRKFourteenCentralBounds
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem second_three_four_no_thirteen {rs : Square} : ¬KRKThirteenGeometry.Clear ((3 : Fin 8),4) rs (2,2) := by
  intro clear
  have shape := KRKThirteenInteriorBarriers.second_entry_necessary clear
  simp only [square_eq_iff,Fin.ext_iff] at shape
  dsimp [dInf,absDiff] at shape
  omega

theorem second_upper_row_no_thirteen {sk rs : Square}
    (king : (sk.1.val = 3 ∧ sk.2.val = 4) ∨ sk.2.val = 5)
    (ry : rs.2.val = 3) : ¬KRKThirteenGeometry.Clear sk rs (2,2) := by
  intro clear
  have shape := KRKThirteenInteriorBarriers.second_entry_necessary clear
  simp only [square_eq_iff,Fin.ext_iff] at shape
  dsimp [dInf,absDiff] at shape
  omega

theorem near_three_four_file_two_no_thirteen {rs : Square} (rx : rs.1.val = 2) (notThree : rs.2.val ≠ 3) : ¬KRKThirteenGeometry.Clear (3,4) rs (1,2) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((3,4) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    dsimp [dInf,absDiff] at distance
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((3,4) : Square) _ (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem near_three_three_row_four_no_thirteen {r : Fin 8} (notOne : r ≠ 1) : ¬KRKThirteenGeometry.Clear (3,3) (r,4) (1,2) := by
  intro clear
  have notFile : r.val ≠ 1 := fun eq => notOne (Fin.ext eq)
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((3,3) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) (r,4) (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    dsimp [dInf,absDiff] at distance
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((3,3) : Square) _ (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem near_upper_low_rook_no_thirteen {k : Fin 8} {rs : Square} (rx : rs.1.val = 2) (height : rs.2.val ≤ 1) : ¬KRKThirteenGeometry.Clear (k,5) rs (1,2) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((k,5) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    dsimp [dInf,absDiff] at distance
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((k,5) : Square) _ (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem near_upper_three_high_no_thirteen {rs : Square} (rx : rs.1.val = 2) (height : 4 ≤ rs.2.val) : ¬KRKThirteenGeometry.Clear (3,5) rs (1,2) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((3,5) : Square) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    dsimp [dInf,absDiff] at distance
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega
  · change KRKTwelveGlobal.Region ((3,5) : Square) _ (1,2) at region
    have shape := KRKThirteenInteriorBarriers.near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    (try simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false])
    all_goals omega

theorem upper_two_above_no_clear {r : Fin 8} (height : 6 ≤ r.val) :
    ¬KRKFourteenGeometry.Clear ((2 : Fin 8),5) (2,r) (1,3) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard ((2 : Fin 8),5) (2,r) (1,3) (2,3) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp
    simp_all [show ((5 : Fin 8).val) = 5 from rfl,show ((3 : Fin 8).val) = 3 from rfl] <;> omega
  have corner := KRKFourteenGeometry.thirteen_deep_corner (by decide) (clear.2.2 _ guard)
  dsimp [KRKTwelveDeepExact.SecondCorner] at corner
  omega

end EndgameChess.Rules.KRKFourteenCentralBounds
