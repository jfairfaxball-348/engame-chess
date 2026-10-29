import EndgameChess.Rules.KRKTwelveGeometry

namespace EndgameChess.Rules.KRKElevenNearBoundary
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000

private theorem near_region {sk rs : Square} (region : KRKTenGlobal.Region sk rs (1,2)) :
    KRKTenNearStrip.Region sk rs := by
  simpa [KRKTenGlobal.Region,KRKTenInteriorExact.Region,KRKEightInteriorExact.stripFrame,
    KRKEdgeDepth.depth,Frame.ofSym,symId] using region

/-- Necessary and sufficient rook-entry condition at the upper boundary.
All king entries are excluded by the ten-ply near-strip inequalities. -/
def UpperEntry (sk rs : Square) : Prop :=
  (sk.1.val = 0 ∧ 4 ≤ rs.2.val) ∨ (sk.1.val = 1 ∧ 3 ≤ rs.2.val)

theorem upper_necessary {sk rs : Square} (sy : sk.2.val = 4) (rx : rs.1.val = 3)
    (clear : KRKElevenGeometry.Clear sk rs (1,2)) : UpperEntry sk rs := by
  rcases clear with immediate | ⟨i,distance,_,_,region⟩ | ⟨i,equal,a,v,sees,_,_,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
      KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · change dInf sk (KRKElevenSlots.point i) = 1 at distance
    change KRKTenGlobal.Region (KRKElevenSlots.point i) rs (1,2) at region
    have shape := near_region region
    dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
      KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper,dInf,absDiff] at shape distance
    omega
  · have shape := near_region region
    have line := sees.1
    change RookLine rs (a.target rs v) at line
    change KRKTenNearStrip.Region sk (a.target rs v) at shape
    dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
      KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper,RookLine,UpperEntry] at shape line ⊢
    omega

theorem two_four_not_clear {sk rs : Square} (sx : sk.1.val = 2) (sy : sk.2.val = 4)
    (rx : rs.1.val = 3) : ¬KRKElevenGeometry.Clear sk rs (1,2) := by
  intro clear
  have condition := upper_necessary sy rx clear
  dsimp [UpperEntry] at condition
  omega

theorem upper_sufficient {sk rs : Square} (sy : sk.2.val = 4) (rx : rs.1.val = 3)
    (entry : UpperEntry sk rs) : KRKElevenGeometry.Clear sk rs (1,2) := by
  let nr : Square := (2,rs.2)
  have shape : KRKTenNearStrip.Upper sk nr := by
    dsimp [UpperEntry] at entry
    dsimp [KRKTenNearStrip.Upper,nr]
    exact ⟨sy,rfl,entry⟩
  have region : KRKTenGlobal.Region sk nr (1,2) := by
    change KRKTenInteriorExact.Region sk nr (1,2)
    exact ⟨rfl,Or.inr ⟨rfl,Or.inr (Or.inr (Or.inr shape))⟩⟩
  have sees : RookSees rs nr sk (1,2) := by
    dsimp [UpperEntry] at entry
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,nr,rx,sy]
    simp <;> omega
  apply KRKElevenGeometry.rook_step_clear sees ?_ ?_ region
  · dsimp [UpperEntry] at entry
    simp only [ne_iff_coords,nr,sy]
    dsimp
    omega
  · simp [nr,ne_iff_coords]

end EndgameChess.Rules.KRKElevenNearBoundary
