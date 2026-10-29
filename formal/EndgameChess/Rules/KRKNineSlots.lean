import EndgameChess.Rules.KRKEightGlobal

namespace EndgameChess.Rules.KRKNineSlots
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

private theorem corner_bounds {sk rs : Square} (seven : KRKSevenCorner.Seven sk rs) : sk.2.val ≤ 4 := by
  rcases seven with (⟨i,entry⟩ | ⟨i,entry⟩) | (⟨i,equal,_⟩ | ⟨i,equal,_⟩)
  · have distance := entry.1
    cases i <;> dsimp [KRKSevenCorner.king,dInf,absDiff] at distance <;> omega
  · have distance := entry.1
    cases i <;> dsimp [KRKSevenCorner.king,symSwap,dInf,absDiff] at distance <;> omega
  · have y := congrArg (fun s : Square => s.2.val) equal
    cases i <;> dsimp [KRKSevenCorner.king] at y <;> omega
  · have y := congrArg (fun s : Square => s.1.val) equal
    cases i <;> dsimp [KRKSevenCorner.king,symSwap] at y <;> omega

private theorem near_bounds {sk rs : Square} (seven : KRKSevenNear.Seven sk rs) :
    sk.1.val ≤ 4 ∧ sk.2.val ≤ 3 := by
  rcases seven with ⟨i,_,distance,_,_⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenNear.king,dInf,absDiff] at distance <;> omega
  · have x := congrArg (fun s : Square => s.1.val) equal
    have y := congrArg (fun s : Square => s.2.val) equal
    cases i <;> dsimp [KRKSevenNear.king] at x y <;> omega

private theorem second_bounds {sk rs : Square} (seven : KRKSevenSecond.Seven sk rs) : sk.2.val ≤ 3 := by
  rcases seven with ⟨i,_,distance⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenSecond.king,dInf,absDiff] at distance <;> omega
  · have y := congrArg (fun s : Square => s.2.val) equal
    cases i <;> dsimp [KRKSevenSecond.king] at y <;> omega

private theorem middle_bounds {sk rs wk : Square} (five : KRKFiveMiddle.BottomFive sk rs wk) : sk.2.val ≤ 3 := by
  dsimp [KRKFiveMiddle.BottomFive] at five
  split at five <;>
    dsimp [KRKFiveMiddle.Five,KRKFiveMiddle.KingEntries,KRKFiveMiddle.RookEntries,dInf,absDiff] at five <;>
    simp only [square_eq_iff,Fin.ext_iff] at five <;> (try dsimp [symX] at five) <;> omega

theorem seven_test_rank {sk rs t : Square} (test : KRKEightEdge.SevenTest sk rs t) : sk.2.val ≤ 4 := by
  rcases test with ⟨_,corner⟩ | ⟨_,near⟩ | ⟨_,second⟩ | ⟨_,middle⟩ | ⟨_,west⟩ | ⟨_,inner⟩
  · exact corner_bounds corner
  · have bound := (near_bounds near).2; omega
  · have bound := second_bounds second; omega
  · have bound := middle_bounds middle; omega
  · exact (near_bounds west).1
  · dsimp [KRKSevenInner.Seven,KRKSevenInner.HorizontalRook,dInf,absDiff] at inner
    simp only [square_eq_iff,Fin.ext_iff] at inner
    dsimp [symSwap] at inner
    omega

theorem edge_rank {sk rs wk : Square} (region : KRKEightEdge.Region sk rs wk) : sk.2.val ≤ 4 := by
  obtain ⟨i,guard⟩ := region.2.1
  exact seven_test_rank (region.2.2 i guard)

abbrev Kind := Fin 8 × Fin 5

def point (i : Kind) : Square := (i.1,⟨i.2.val,by have := i.2.isLt; omega⟩)

def frame (wk : Square) : Frame :=
  if KRKEdgeDepth.depth wk = 0 then normalize wk else KRKEightInteriorExact.stripFrame wk

theorem region_rank {sk rs wk : Square} (region : KRKEightGlobal.Region sk rs wk) :
    ((frame wk).f sk).2.val ≤ 4 := by
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · simp only [frame,edge,↓reduceIte]
    simp only [KRKEightGlobal.Region,edge,↓reduceIte] at region
    exact edge_rank region
  · simp only [frame,edge,↓reduceIte]
    simp only [KRKEightGlobal.Region,edge,↓reduceIte,KRKEightInteriorExact.Region] at region
    rcases region.2 with ⟨_,inner⟩ | ⟨_,near⟩
    · dsimp [KRKEightInner.Region,KRKEightInner.Horizontal,symSwap] at inner
      omega
    · have shape := near.2.2.2.1
      exact Nat.le_trans (Nat.le_of_eq shape) (by decide)

theorem region_point {sk rs wk : Square} (region : KRKEightGlobal.Region sk rs wk) :
    ∃ i : Kind, (frame wk).f sk = point i := by
  let i : Kind := (((frame wk).f sk).1,⟨((frame wk).f sk).2.val,by have := region_rank region; omega⟩)
  exact ⟨i,Prod.ext rfl (Fin.ext rfl)⟩

end EndgameChess.Rules.KRKNineSlots
