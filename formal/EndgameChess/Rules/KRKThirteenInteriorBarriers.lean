import EndgameChess.Rules.KRKFourteenDeepStrip

namespace EndgameChess.Rules.KRKThirteenInteriorBarriers
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem second_region_iff {sk rs : Square} : KRKTwelveGlobal.Region sk rs (2,2) ↔ KRKTwelveSecondCorner.Region sk rs := by
  simp [KRKTwelveGlobal.Region,KRKEdgeDepth.depth,KRKTwelveInteriorExact.Region,KRKTwelveDeepExact.Region,
    KRKTwelveDeepExact.SecondCorner,KRKTenInterior.cornerSym,Frame.ofSym,symId]

theorem near_region_iff {sk rs : Square} : KRKTwelveGlobal.Region sk rs (1,2) ↔ KRKTwelveNearExact.Region sk rs := by
  simp [KRKTwelveGlobal.Region,KRKEdgeDepth.depth,KRKTwelveInteriorExact.Region,KRKTwelveInteriorExact.StripRegion,
    KRKEightInteriorExact.stripFrame,Frame.ofSym,symId,show ((3 : Fin 8).val) = 3 from rfl]

theorem central_region_iff {sk rs : Square} : KRKTwelveGlobal.Region sk rs (1,3) ↔ KRKTwelveCentralExact.Region sk rs := by
  simp [KRKTwelveGlobal.Region,KRKEdgeDepth.depth,KRKTwelveInteriorExact.Region,KRKTwelveInteriorExact.StripRegion,
    KRKEightInteriorExact.stripFrame,Frame.ofSym,symId,show ((3 : Fin 8).val) = 3 from rfl]

/-- All ordinary entries into the second-corner twelve-ply region. -/
theorem second_entry_necessary {sk rs : Square} (clear : KRKThirteenGeometry.Clear sk rs (2,2)) :
    (dInf sk (4,1) = 1 ∧ rs.2.val = 3 ∧ 4 ≤ rs.1.val) ∨
    (dInf sk (1,4) = 1 ∧ rs.1.val = 3 ∧ 4 ≤ rs.2.val) ∨
    sk = ((4 : Fin 8),1) ∨ sk = ((1 : Fin 8),4) := by
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 2 = 0 at zero
    contradiction
  · change dInf sk (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (2,2) at region
    have shape := second_region_iff.mp region
    rcases shape with ⟨sx,sy,ry,width⟩ | ⟨sy,sx,rx,height⟩
    · have eq : KRKThirteenSlots.point i = ((4 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      rw [eq] at distance
      exact Or.inl ⟨distance,ry,width⟩
    · have eq : KRKThirteenSlots.point i = ((1 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      rw [eq] at distance
      exact Or.inr (Or.inl ⟨distance,rx,height⟩)
  · change KRKTwelveGlobal.Region sk _ (2,2) at region
    have shape := second_region_iff.mp region
    rcases shape with ⟨sx,sy,_,_⟩ | ⟨sy,sx,_,_⟩
    · exact Or.inr (Or.inr (Or.inl (Prod.ext (Fin.ext sx) (Fin.ext sy))))
    · exact Or.inr (Or.inr (Or.inr (Prod.ext (Fin.ext sx) (Fin.ext sy))))

theorem central_four_four_no_thirteen {rs : Square} (rx : rs.1.val = 2) :
    ¬KRKThirteenGeometry.Clear ((4 : Fin 8),4) rs (1,3) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf ((4 : Fin 8),4) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,3) at region
    have shape := central_region_iff.mp region
    dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,
      KRKTwelveCentralExact.Opposition] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp [dInf,absDiff] at distance
    dsimp at shape
    omega
  · change KRKTwelveGlobal.Region ((4 : Fin 8),4) _ (1,3) at region
    have shape := central_region_iff.mp region
    dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,
      KRKTwelveCentralExact.Opposition] at shape
    simp only [square_eq_iff,Fin.ext_iff] at shape
    dsimp at shape
    omega

theorem near_upper_no_thirteen {k : Fin 8} {rs : Square} (rx : rs.1.val = 3) (height : 3 ≤ rs.2.val) :
    ¬KRKThirteenGeometry.Clear (k,5) rs (1,2) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · change dInf (k,(5 : Fin 8)) (KRKThirteenSlots.point i) = 1 at distance
    change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,2) at region
    have shape := near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
      KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    dsimp [dInf,absDiff] at distance
    omega
  · change KRKTwelveGlobal.Region (k,(5 : Fin 8)) _ (1,2) at region
    have shape := near_region_iff.mp region
    dsimp [KRKTwelveNearExact.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
      KRKTwelveNearFileOne.Region,KRKTwelveNearUpper.Region,KRKTwelveNearExact.RowTwo] at shape
    omega

end EndgameChess.Rules.KRKThirteenInteriorBarriers
