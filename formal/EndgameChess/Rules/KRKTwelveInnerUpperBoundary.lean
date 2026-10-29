import EndgameChess.Rules.KRKTwelveInnerUpperFour

namespace EndgameChess.Rules.KRKTwelveInnerUpperBoundary
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private theorem corner_eight_file {sk rs : Square} (apart : sk ≠ rs)
    (region : KRKEightEdge.Region sk rs (0,0)) : sk.1.val ≤ 4 := by
  have clear := (KRKEightEdge.clear_iff (wk := ((0 : Fin 8),0)) rfl (by decide) apart).mpr region
  have mapped := KRKCastleEight.frame_map (Frame.ofSym symSwap) apart clear
  have evaluated := (KRKEightEdge.clear_iff (wk := ((0 : Fin 8),0)) rfl (by decide)
    ((Frame.ofSym symSwap).ne_iff.mpr apart)).mp mapped
  exact KRKNineSlots.edge_rank evaluated

private theorem near_low_king {sk : Square} (sx : 4 ≤ sk.1.val)
    (seven : KRKSevenNear.Seven sk (4,1)) : sk.1.val = 4 ∧ sk.2.val ≤ 1 := by
  rcases seven with ⟨i,shape,distance,_,_⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenNear.king,KRKSevenNear.RookRegion,KRKSevenNear.LowRegion,
      KRKSevenNear.SideRegion,dInf,absDiff] at shape distance <;> omega
  · have file := congrArg (fun t : Square => t.1.val) equal
    cases i <;> dsimp [KRKSevenNear.king] at file <;> omega

private theorem corner_high_no_eight {sk : Square} (apart : sk ≠ ((4 : Fin 8),1))
    (sx : 4 ≤ sk.1.val) (sy : 1 ≤ sk.2.val) : ¬KRKEightEdge.Region sk (4,1) (0,0) := by
  intro region
  have guard : KRKCornerWeakBand.Guard sk ((4 : Fin 8),1) (0,0) (1,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  have near : KRKSevenNear.Seven sk (4,1) := by
    have test := region.2.2 .east guard
    simpa [KRKEightEdge.SevenTest,KRKEightEdge.destination,KRKEightEdge.right] using test
  have bound := near_low_king sx near
  have rank : sk.2.val = 1 := by omega
  have equal : sk = ((4 : Fin 8),1) := Prod.ext (Fin.ext bound.1) (Fin.ext rank)
  exact apart equal

private theorem corner_five_two_no_nine : ¬KRKNineGeometry.Clear ((5 : Fin 8),2) (4,1) (0,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),2) (KRKNineSlots.point i) = 1 at distance
    change KRKNineSlots.point i ≠ ((4 : Fin 8),1) at apart
    change KRKEightEdge.Region (KRKNineSlots.point i) (4,1) (0,0) at region
    have sx : 4 ≤ (KRKNineSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have sy : 1 ≤ (KRKNineSlots.point i).2.val := by dsimp [dInf,absDiff] at distance; omega
    exact corner_high_no_eight apart sx sy region
  · change _ ≠ ((5 : Fin 8),2) at notKing
    change KRKEightEdge.Region ((5 : Fin 8),2) _ (0,0) at region
    have bound := corner_eight_file notKing.symm region
    change 5 ≤ 4 at bound
    contradiction

private theorem covered_of_no_test {sk rs wk : Square} {i : KRKEightEdge.Reply}
    (region : KRKTenEdge.Region sk rs wk)
    (distance : dInf wk (KRKEightEdge.destination wk i) = 1)
    (noTest : ¬KRKTenEdge.NineTest sk rs (KRKEightEdge.destination wk i)) :
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
  exact False.elim (noTest (region.2.2 i ⟨distance,notRook,by change 2 ≤ dInf sk t; omega,fun h => line h.1⟩))

private theorem near_five_two_no_eleven : ¬KRKElevenGeometry.Clear ((5 : Fin 8),2) (4,2) (1,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),2) (KRKElevenSlots.point i) = 1 at distance
    change KRKTenEdge.Region (KRKElevenSlots.point i) (4,2) (1,0) at region
    have sx : 4 ≤ (KRKElevenSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have guard : KRKCornerWeakBand.Guard (KRKElevenSlots.point i) ((4 : Fin 8),2) (1,0) (2,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp; omega
    have near : KRKNineNearStrip.Nine (symSwap.f (KRKElevenSlots.point i)) (symSwap.f ((4 : Fin 8),2)) := by
      have test := region.2.2 .northEast guard
      simpa [KRKTenEdge.NineTest,KRKEightEdge.destination,KRKEightEdge.right] using test
    have bound := KRKElevenEdgeBoundary.near_rank_bound near
    dsimp [symSwap] at bound
    omega
  · let nr := a.target ((4 : Fin 8),2) v
    change RookSees ((4 : Fin 8),2) nr (5,2) (1,0) at sees
    change nr ≠ ((5 : Fin 8),2) at notKing
    change KRKTenEdge.Region ((5 : Fin 8),2) nr (1,0) at region
    have a := covered_box (covered_of_no_test (i := .north) region (by decide) (by
      intro test
      have inner : KRKNineInner.Nine ((5 : Fin 8),2) nr := by
        simpa [KRKTenEdge.NineTest,KRKEightEdge.destination] using test
      have bound := KRKElevenEdgeBoundary.inner_file_bound inner
      change 5 ≤ 4 at bound
      contradiction))
    have b := covered_box (covered_of_no_test (i := .northEast) region (by decide) (by
      intro test
      have near : KRKNineNearStrip.Nine (symSwap.f ((5 : Fin 8),2)) (symSwap.f nr) := by
        simpa [KRKTenEdge.NineTest,KRKEightEdge.destination,KRKEightEdge.right] using test
      have bound := KRKElevenEdgeBoundary.near_rank_bound near
      change 5 ≤ 2 at bound
      contradiction))
    dsimp [KRKEightEdge.destination,KRKEightEdge.right] at a b
    have rank : nr.2.val = 1 := by omega
    have file : nr.1.val = 4 := by
      have line := sees.1
      dsimp [RookLine] at line
      omega
    have equal : nr = ((4 : Fin 8),1) := Prod.ext (Fin.ext file) (Fin.ext rank)
    have ten := (KRKTenEdge.clear_iff (wk := ((1 : Fin 8),0)) rfl (by decide) notKing.symm).mpr region
    rw [equal] at ten
    have guard : KRKCornerWeakBand.Guard ((5 : Fin 8),2) (4,1) (1,0) (0,0) := by
      dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    exact corner_five_two_no_nine (ten.2.2 _ guard)

private theorem third_second_no_eleven {k : Fin 8} : ¬KRKElevenGeometry.Clear (5,k) (3,2) (2,0) := by
  intro clear
  rcases clear with immediate | ⟨i,distance,apart,far,region⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf ((5 : Fin 8),k) (KRKElevenSlots.point i) = 1 at distance
    change KRKTenEdge.Region (KRKElevenSlots.point i) (3,2) (2,0) at region
    have sx : 4 ≤ (KRKElevenSlots.point i).1.val := by dsimp [dInf,absDiff] at distance; omega
    have guard : KRKCornerWeakBand.Guard (KRKElevenSlots.point i) ((3 : Fin 8),2) (2,0) (2,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp; omega
    have near : KRKNineNearStrip.Nine (symSwap.f (KRKElevenSlots.point i)) (symSwap.f ((3 : Fin 8),2)) := by
      have test := region.2.2 .north guard
      simpa [KRKTenEdge.NineTest,KRKEightEdge.destination] using test
    have bound := KRKElevenEdgeBoundary.near_rank_bound near
    dsimp [symSwap] at bound
    omega
  · let nr := a.target ((3 : Fin 8),2) v
    change RookSees ((3 : Fin 8),2) nr (5,k) (2,0) at sees
    change nr ≠ ((5 : Fin 8),k) at notKing
    change KRKTenEdge.Region ((5 : Fin 8),k) nr (2,0) at region
    have a := covered_box (covered_of_no_test (i := .northWest) region (by decide) (by
      intro test
      have inner : KRKNineInner.Nine ((5 : Fin 8),k) nr := by
        simpa [KRKTenEdge.NineTest,KRKEightEdge.destination,KRKEightEdge.left] using test
      have bound := KRKElevenEdgeBoundary.inner_file_bound inner
      change 5 ≤ 4 at bound
      contradiction))
    have b := covered_box (covered_of_no_test (i := .north) region (by decide) (by
      intro test
      have near : KRKNineNearStrip.Nine (symSwap.f ((5 : Fin 8),k)) (symSwap.f nr) := by
        simpa [KRKTenEdge.NineTest,KRKEightEdge.destination] using test
      have bound := KRKElevenEdgeBoundary.near_rank_bound near
      change 5 ≤ 2 at bound
      contradiction))
    dsimp [KRKEightEdge.destination,KRKEightEdge.left] at a b
    have rank : nr.2.val = 1 := by omega
    have file : nr.1.val = 3 := by
      have line := sees.1
      dsimp [RookLine] at line
      omega
    have safe := region.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega

theorem upper_three_no_clear {k : Fin 8} : ¬KRKTwelveGeometry.Clear (k,5) (2,3) (1,1) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard (k,5) (2,3) (1,1) (0,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  have mapped := KRKElevenGeometry.frame_map (Frame.ofSym symSwap)
    (by simp only [ne_iff_coords]; dsimp; omega)
    (by simp only [ne_iff_coords]; dsimp; omega) (by decide)
    (by dsimp [dInf,absDiff]; omega) (by simp [RookSees,RookLine,OnSeg,show ((3 : Fin 8).val) = 3 from rfl]) (clear.2.2 _ guard)
  exact third_second_no_eleven mapped

theorem two_five_four_no_clear : ¬KRKTwelveGeometry.Clear ((2 : Fin 8),5) (2,4) (1,1) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard ((2 : Fin 8),5) (2,4) (1,1) (0,1) := by
    dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
  have mapped := KRKElevenGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide) (by decide) (by decide)
    (by dsimp [RookSees,RookLine,OnSeg]; decide) (clear.2.2 _ guard)
  exact near_five_two_no_eleven mapped

theorem five_necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val ≤ 2)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) (clear : KRKTwelveGeometry.Clear sk rs (1,1)) :
    sk = ((1 : Fin 8),5) ∧ rs = ((2 : Fin 8),4) := by
  have height : 3 ≤ rs.2.val := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have kingEq : sk = (sk.1,(5 : Fin 8)) := Prod.ext rfl (Fin.ext sy)
  have notThree : rs.2.val ≠ 3 := by
    intro three
    have rookEq : rs = ((2 : Fin 8),3) := Prod.ext (Fin.ext rx) (Fin.ext three)
    rw [kingEq,rookEq] at clear
    exact upper_three_no_clear clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,1) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
    dsimp; omega
  have sharp := KRKTwelveInner.near_guard_sharp apart (by dsimp [dInf,absDiff]; omega) clear guard
  have below := sharp.2.1
  have zero := sharp.2.2.1
  have one := sharp.2.2.2
  have notTwoFour : ¬(sk.1.val = 2 ∧ rs.2.val = 4) := by
    rintro ⟨two,four⟩
    have kingEq : sk = ((2 : Fin 8),5) := Prod.ext (Fin.ext two) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),4) := Prod.ext (Fin.ext rx) (Fin.ext four)
    rw [kingEq,rookEq] at clear
    exact two_five_four_no_clear clear
  have shape : sk.1.val = 1 ∧ rs.2.val = 4 := by omega
  exact ⟨Prod.ext (Fin.ext shape.1) (Fin.ext sy),Prod.ext (Fin.ext rx) (Fin.ext shape.2)⟩

end EndgameChess.Rules.KRKTwelveInnerUpperBoundary
