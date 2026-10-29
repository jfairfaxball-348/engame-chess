import EndgameChess.Rules.KRKNineGeometry

namespace EndgameChess.Rules.KRKNineInnerBoundary
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000

theorem inner_region {sk rs : Square} (region : KRKEightGlobal.Region sk rs (1,1)) :
    KRKEightInner.Region sk rs := by
  change KRKEightInteriorExact.Region sk rs (1,1) at region
  rcases region.2 with ⟨_,inner⟩ | ⟨bad,_⟩
  · exact inner
  · change 1 = 2 at bad
    contradiction

private theorem frame_f (s : Square) : (KRKNineSlots.frame ((1 : Fin 8),1)).f s = s := rfl
private theorem frame_r (s : Square) : (KRKNineSlots.frame ((1 : Fin 8),1)).r s = s := rfl

theorem rook_two_zero_high {sk : Square} (high : sk.2.val = 4) :
    ¬KRKNineGeometry.Clear sk ((2 : Fin 8),0) (1,1) := by
  intro clear
  rcases clear with immediate | points | rays
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · simp only [KRKNineGeometry.KingPoints,frame_f,frame_r] at points
    obtain ⟨_,_,_,_,region⟩ := points
    have inner := inner_region region
    dsimp [KRKEightInner.Region,KRKEightInner.Horizontal,symSwap] at inner
    omega
  · simp only [KRKNineGeometry.RookRays,frame_f,frame_r] at rays
    obtain ⟨_,_,_,_,_,_,_,region⟩ := rays
    have inner := inner_region region
    dsimp [KRKEightInner.Region,KRKEightInner.Horizontal,symSwap] at inner
    omega

theorem rook_two_three_right_high {sk : Square} (file : sk.1.val = 3) (high : 3 ≤ sk.2.val) :
    ¬KRKNineGeometry.Clear sk ((2 : Fin 8),3) (1,1) := by
  intro clear
  rcases clear with immediate | points | rays
  · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
    change 1 = 0 at zero
    contradiction
  · simp only [KRKNineGeometry.KingPoints,frame_f,frame_r] at points
    obtain ⟨i,distance,_,_,region⟩ := points
    have inner := inner_region region
    dsimp [KRKEightInner.Region,KRKEightInner.Horizontal,symSwap] at inner
    dsimp [dInf,absDiff] at distance
    omega
  · simp only [KRKNineGeometry.RookRays,frame_f,frame_r] at rays
    obtain ⟨_,_,_,_,_,_,_,region⟩ := rays
    have inner := inner_region region
    dsimp [KRKEightInner.Region,KRKEightInner.Horizontal,symSwap] at inner
    omega

end EndgameChess.Rules.KRKNineInnerBoundary
