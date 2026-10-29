import EndgameChess.Rules.KRKElevenEntry

namespace EndgameChess.Rules.KRKElevenSlots
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private theorem corner_file {sk rs : Square} (seven : KRKSevenCorner.Seven sk rs) : sk.1.val ≤ 4 := by
  rcases seven with (⟨i,entry⟩ | ⟨i,entry⟩) | (⟨i,equal,_⟩ | ⟨i,equal,_⟩)
  · have distance := entry.1
    cases i <;> dsimp [KRKSevenCorner.king,dInf,absDiff] at distance <;> omega
  · have distance := entry.1
    cases i <;> dsimp [KRKSevenCorner.king,symSwap,dInf,absDiff] at distance <;> omega
  · have x := congrArg (fun s : Square => s.1.val) equal
    cases i <;> dsimp [KRKSevenCorner.king] at x <;> omega
  · have x := congrArg (fun s : Square => s.2.val) equal
    cases i <;> dsimp [KRKSevenCorner.king,symSwap] at x <;> omega

private theorem near_bounds {sk rs : Square} (seven : KRKSevenNear.Seven sk rs) :
    sk.1.val ≤ 4 ∧ sk.2.val ≤ 3 := by
  rcases seven with ⟨i,_,distance,_,_⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenNear.king,dInf,absDiff] at distance <;> omega
  · have x := congrArg (fun s : Square => s.1.val) equal
    have y := congrArg (fun s : Square => s.2.val) equal
    cases i <;> dsimp [KRKSevenNear.king] at x y <;> omega

private theorem second_file {sk rs : Square} (seven : KRKSevenSecond.Seven sk rs) : sk.1.val ≤ 4 := by
  rcases seven with ⟨i,_,distance⟩ | ⟨i,equal,_⟩
  · cases i <;> dsimp [KRKSevenSecond.king,dInf,absDiff] at distance <;> omega
  · have x := congrArg (fun s : Square => s.1.val) equal
    cases i <;> dsimp [KRKSevenSecond.king] at x <;> omega

private theorem near_edge_file {sk rs : Square} (region : KRKEightEdge.Region sk rs (1,0)) : sk.1.val ≤ 4 := by
  obtain ⟨i,guard⟩ := region.2.1
  have test := region.2.2 i guard
  have width : (KRKEightEdge.destination (1,0) i).1.val ≤ 2 := by
    cases i <;> decide
  rcases test with ⟨_,corner⟩ | ⟨_,near⟩ | ⟨_,second⟩ | ⟨equal,middle⟩ | ⟨_,west⟩ | ⟨_,inner⟩
  · exact corner_file corner
  · exact (near_bounds near).1
  · exact second_file second
  · simp only [square_eq_iff,Fin.ext_iff] at equal
    dsimp at equal
    omega
  · exact Nat.le_trans (near_bounds west).2 (by decide)
  · dsimp [KRKSevenInner.Seven,KRKSevenInner.HorizontalRook,dInf,absDiff] at inner
    simp only [square_eq_iff,Fin.ext_iff] at inner
    dsimp [symSwap] at inner
    omega

private theorem nine_rank {sk rs wk : Square} (rank : wk.2.val = 0) (nine : KRKNineEdge.Nine sk rs wk) : sk.2.val ≤ 5 := by
  rcases nine with immediate | ⟨i,distance,_,_,_⟩ | ⟨i,equal,_⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · have bound := i.2.isLt
    dsimp [KRKNineSlots.point,dInf,absDiff] at distance
    omega
  · have rank := congrArg (fun t : Square => t.2.val) equal
    have bound := i.2.isLt
    dsimp [KRKNineSlots.point] at rank
    omega

private theorem nine_near_file {sk rs : Square} (nine : KRKNineEdge.Nine sk rs (1,0)) : sk.1.val ≤ 5 := by
  rcases nine with immediate | ⟨i,distance,_,_,region⟩ | ⟨i,equal,a,v,_,_,_,region⟩
  · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    omega
  · have bound := near_edge_file region
    dsimp [dInf,absDiff] at distance
    omega
  · exact Nat.le_trans (near_edge_file region) (by decide)

theorem nine_test_rank {sk rs t : Square} (test : KRKTenEdge.NineTest sk rs t) : sk.2.val ≤ 5 := by
  rcases test with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
  · exact nine_rank rfl h
  · exact nine_rank rfl h
  · exact nine_rank rfl h
  · exact nine_rank rfl h
  · have bound := nine_rank rfl h
    simpa only [symX] using bound
  · exact nine_near_file h
  · rcases h with (⟨i,distance,_,_⟩ | ⟨i,distance,_,_⟩) | (⟨i,equal,_⟩ | ⟨i,equal,_⟩)
    all_goals cases i <;> dsimp [KRKNineInner.king,symSwap,dInf,absDiff] at * <;>
      simp only [square_eq_iff,Fin.ext_iff] at * <;> omega
  · dsimp [KRKNineNearStrip.Nine,symSwap,dInf,absDiff] at h
    simp only [square_eq_iff,Fin.ext_iff] at h
    omega

abbrev Kind := Fin 8 × Fin 6

def point (i : Kind) : Square := (i.1,⟨i.2.val,by have := i.2.isLt; omega⟩)

def frame (wk : Square) : Frame :=
  if KRKEdgeDepth.depth wk = 0 then normalize wk else KRKEightInteriorExact.stripFrame wk

theorem region_rank {sk rs wk : Square} (region : KRKTenGlobal.Region sk rs wk) :
    ((frame wk).f sk).2.val ≤ 5 := by
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · simp only [frame,edge,↓reduceIte]
    simp only [KRKTenGlobal.Region,edge,↓reduceIte] at region
    obtain ⟨i,guard⟩ := region.2.1
    exact nine_test_rank (region.2.2 i guard)
  · simp only [frame,edge,↓reduceIte]
    simp only [KRKTenGlobal.Region,edge,↓reduceIte,KRKTenInteriorExact.Region] at region
    rcases region.2 with ⟨_,inner⟩ | ⟨_,near⟩
    · dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
        KRKTenInner.SideExtra,KRKTenInner.HighExtra,symSwap] at inner
      omega
    · dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
        KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper] at near
      omega

theorem region_point {sk rs wk : Square} (region : KRKTenGlobal.Region sk rs wk) :
    ∃ i : Kind, (frame wk).f sk = point i := by
  let i : Kind := (((frame wk).f sk).1,⟨((frame wk).f sk).2.val,by have := region_rank region; omega⟩)
  exact ⟨i,Prod.ext rfl (Fin.ext rfl)⟩

end EndgameChess.Rules.KRKElevenSlots
