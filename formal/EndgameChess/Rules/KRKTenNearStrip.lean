import EndgameChess.Rules.KRKTenCentralStrip
import EndgameChess.Rules.KRKNineSecondBoundary
import EndgameChess.Rules.KRKNineUpperEntries

namespace EndgameChess.Rules.KRKTenNearStrip
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

theorem lower_neighbour_covered {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKTenGeometry.Clear sk rs (1,2)) : Covered sk rs (2,1) := by
  by_cases king : dInf sk (2,1) ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs (2,1)
  · exact Or.inr line
  have notRook : ((2 : Fin 8),1) ≠ rs := by
    intro equal
    have safe := clear.1
    rw [←equal] at safe
    dsimp [SafeRook,dInf,absDiff] at safe king
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (2,1) :=
    ⟨by decide,notRook,by omega,fun sees => line sees.1⟩
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKNineGeometry.frame_map g distinct
    notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have condition := (KRKNineNearStrip.clear_iff (g.ne_iff.mpr distinct)
    (g.ne_iff.mpr notKing)
    (g.ne_iff.mpr notRook.symm) (by
      change 2 ≤ dInf (g.f sk) (g.f ((2 : Fin 8),1))
      rw [g.distance]; exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mp mapped
  have cover := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,2))
    (by decide) (Or.inl (by decide)))
  dsimp [KRKNineNearStrip.Nine,g,Frame.ofSym,symSwap,dInf,absDiff] at condition
  simp only [square_eq_iff,Fin.ext_iff] at condition
  dsimp [dInf,absDiff] at far
  dsimp at condition cover
  omega

theorem no_lower_guard {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKTenGeometry.Clear sk rs (1,2)) : ¬KRKCornerWeakBand.Guard sk rs (1,2) (2,1) := by
  intro guard
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKNineGeometry.frame_map g distinct notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have condition := (KRKNineNearStrip.clear_iff (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing)
    (g.ne_iff.mpr guard.2.1.symm) (by
      change 2 ≤ dInf (g.f sk) (g.f ((2 : Fin 8),1)); rw [g.distance]; exact guard.2.2.1)
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mp mapped
  have cover := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,2))
    (by decide) (Or.inl (by decide)))
  dsimp [KRKNineNearStrip.Nine,g,Frame.ofSym,symSwap,dInf,absDiff] at condition
  simp only [square_eq_iff,Fin.ext_iff] at condition
  dsimp [dInf,absDiff] at far
  dsimp at condition cover
  omega

theorem prison {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKTenGeometry.Clear sk rs (1,2)) : KRKEightNearStrip.Prison sk rs := by
  have a := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (1,3)) (by decide)
    (Or.inr (Or.inl ⟨Or.inl rfl,by decide,by decide⟩)))
  have b := covered_box (lower_neighbour_covered distinct far clear)
  have c := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,2)) (by decide) (Or.inl (by decide)))
  have d := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,3)) (by decide) (Or.inl (by decide)))
  have safe := clear.1
  clear clear
  dsimp at a b c d
  have kingFar : 3 ≤ sk.1.val ∨ sk.2.val = 0 ∨ 4 ≤ sk.2.val := by
    dsimp [dInf,absDiff] at far
    omega
  have protection : 3 ≤ rs.1.val ∨ rs.2.val = 0 ∨ 4 ≤ rs.2.val ∨
      (sk.1.val ≤ rs.1.val + 1 ∧ rs.1.val ≤ sk.1.val + 1 ∧
       sk.2.val ≤ rs.2.val + 1 ∧ rs.2.val ≤ sk.2.val + 1) := by
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  clear safe far
  dsimp [KRKEightNearStrip.Prison]
  by_cases file : rs.1.val = 1 <;> by_cases row : rs.2.val = 3 <;> omega

theorem diagonal_near_eight_clear {rs : Square} (distinct : ((2 : Fin 8),2) ≠ rs)
    (safe : SafeRook (2,2) rs (1,0)) :
    KRKEightGeometry.Clear (2,2) rs (1,0) := by
  refine ⟨safe,KRKSevenNear.diagonal_live safe,?_⟩
  intro t guard
  have choices : t = ((0 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨ t = ((0 : Fin 8),1) := by
    have distance := guard.1
    have far := guard.2.2.1
    simp only [square_eq_iff,Fin.ext_iff]
    dsimp [dInf,absDiff] at distance far
    dsimp
    omega
  have test : ∀ {t : Square}, KRKCornerWeakBand.Guard ((2 : Fin 8),2) rs (1,0) t →
      t.1.val ≤ 4 → t.2.val ≤ 1 → KRKEightEdge.SevenTest (2,2) rs t → KRKSevenGeometry.Clear (2,2) rs t := by
    intro t guard x y region
    exact (KRKEightEdge.seven_test_iff distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
      guard.2.1.symm guard.2.2.1 guard.2.2.2 x y).mpr region
  rcases choices with rfl | rfl | rfl
  · apply test guard (by decide) (by decide)
    simpa [KRKEightEdge.SevenTest,KRKSevenCorner.Seven] using
      (Or.inr (Or.inl ⟨.diagonal,rfl,True.intro⟩) : KRKSevenCorner.Seven (2,2) rs)
  · apply test guard (by decide) (by decide)
    simpa [KRKEightEdge.SevenTest,KRKSevenSecond.Seven] using
      (Or.inr ⟨.middle,rfl,True.intro⟩ : KRKSevenSecond.Seven (2,2) rs)
  · apply test guard (by decide) (by decide)
    simpa [KRKEightEdge.SevenTest,KRKSevenNear.Seven] using
      (Or.inr ⟨.diagonal,rfl,True.intro⟩ : KRKSevenNear.Seven (symSwap.f ((2 : Fin 8),2)) (symSwap.f rs))


private theorem second_eight_clear {rs : Square} (rx : rs.1.val = 3) (height : 2 ≤ rs.2.val) :
    KRKEightGeometry.Clear (2,2) rs (2,0) := by
  have distinct : ((2 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,rx]; dsimp; omega
  refine ⟨Or.inl ?_,⟨((1 : Fin 8),0),?_⟩,?_⟩
  · dsimp [dInf,absDiff]; omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx]
    simp <;> omega
  · intro t guard
    have choices : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
      have distance := guard.1
      have far := guard.2.2.1
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp [dInf,absDiff] at distance far
      dsimp
      omega
    rcases choices with rfl | rfl
    · exact (KRKSevenNear.clear_iff distinct guard.2.1.symm guard.2.2.2).mpr
        (Or.inr ⟨.diagonal,rfl,True.intro⟩)
    · apply (KRKSevenMiddle.bottom_clear_iff rfl (by decide) (by decide) distinct
        (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2).mpr
      simp only [KRKFiveMiddle.BottomFive,show ((3 : Fin 8).val) = 3 from rfl,show (3 : Nat) ≤ 3 from by decide,↓reduceIte]
      change KRKFiveMiddle.KingEntries (2,2) rs (3,0) ∨ KRKFiveMiddle.RookEntries (2,2) rs (3,0)
      by_cases tall : 3 ≤ rs.2.val
      · exact Or.inl (Or.inl ⟨tall,by decide⟩)
      · have row : rs.2.val = 2 := by omega
        refine Or.inr (Or.inr (Or.inl ⟨rfl,Or.inr (Or.inr ⟨row,?_⟩)⟩))
        change 3 ≤ rs.1.val
        omega

private theorem edge_reply {sk rs : Square} {j : Fin 8} (sx : sk.1.val = 3) (sy : sk.2.val = 2)
    (ry : rs.2.val = 3) (width : 2 ≤ rs.1.val) (choice : j = 1 ∨ j = 2)
    (guard : KRKCornerWeakBand.Guard sk rs (1,2) (0,j)) : KRKNineGeometry.Clear sk rs (0,j) := by
  have distinct : sk ≠ rs := by simp only [ne_iff_coords,sy,ry]; (try dsimp); omega
  let g := Frame.ofSym symSwap
  have nextDistinct : ((2 : Fin 8),2) ≠ g.f rs := by
    simp only [g,Frame.ofSym,symSwap,ne_iff_coords,ry]; dsimp; omega
  have eight : KRKEightGeometry.Clear (2,2) (g.f rs) (g.f ((0 : Fin 8),j)) := by
    rcases choice with rfl | rfl
    · apply diagonal_near_eight_clear nextDistinct
      apply Or.inl
      dsimp [g,Frame.ofSym,symSwap,dInf,absDiff]
      omega
    · exact second_eight_clear ry width
  have edge : KRKEdgeDepth.depth (g.f ((0 : Fin 8),j)) = 0 := by
    dsimp [g,Frame.ofSym,symSwap,KRKEdgeDepth.depth]; omega
  have region : KRKEightGlobal.Region (2,2) (g.f rs) (g.f ((0 : Fin 8),j)) := by
    simp only [KRKEightGlobal.Region,edge,↓reduceIte]
    exact (KRKEightGlobal.edge_clear_iff nextDistinct edge).mp eight
  have mapped := KRKNineGeometry.king_step_clear (sk := g.f sk) (ns := ((2 : Fin 8),2))
    (by dsimp [g,Frame.ofSym,symSwap,dInf,absDiff]; omega) nextDistinct (by
      rcases choice with rfl | rfl <;> decide) region
  have back := KRKNineGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
    (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega))) (g.ne_iff.mpr guard.2.1.symm)
    (by rw [g.distance]; exact guard.2.2.1) (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
  simpa only [Frame.inverse,g.left_inv] using back

/-- A new ten-ply family, including the protected adjacent rook (2,3). -/
def RowThree (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.2.val = 3 ∧ 2 ≤ rs.1.val

theorem row_three_clear {sk rs : Square} (region : RowThree sk rs) : KRKTenGeometry.Clear sk rs (1,2) := by
  obtain ⟨sx,sy,ry,width⟩ := region
  have safe : SafeRook sk rs (1,2) := by dsimp [SafeRook,dInf,absDiff]; omega
  refine ⟨safe,⟨((0 : Fin 8),1),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry]
    simp <;> omega
  · intro t guard
    have choices : t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases choices with rfl | rfl | rfl
    · exact edge_reply sx sy ry width (Or.inl rfl) guard
    · exact edge_reply sx sy ry width (Or.inr rfl) guard
    · apply KRKNineGeometry.rook_step_clear (nr := ((1 : Fin 8),3))
      · simp only [RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry]; simp <;> omega
      · simp only [ne_iff_coords,sx,sy]; dsimp; omega
      · decide
      · change KRKEightInteriorExact.Region sk ((1 : Fin 8),3) (1,1)
        refine ⟨rfl,Or.inl ⟨rfl,Or.inl ?_⟩⟩
        exact ⟨sx,Or.inr (Or.inr ⟨sy,Or.inr ⟨rfl,by decide⟩⟩)⟩

theorem kernel_row_three_exact_ten {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (region : RowThree sk rs) :
    MateWithin σ 10 q ∧ ¬MateWithin σ 9 q := by
  have far : 2 ≤ dInf sk (1,2) := by dsimp [RowThree,dInf,absDiff] at *; omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  refine ⟨(KRKTenGeometry.kernel_ten_iff material turn notMate).mpr (row_three_clear region),?_⟩
  intro nine
  have eight := KRKEightGeometry.weak_nine_eight material turn nine
  have old := (KRKEightNearStrip.kernel_eight_iff material turn far).mp eight
  have rank := old.2.2.2.1
  have newRank := region.2.1
  omega

theorem file_one_necessary {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 2) (rx : rs.1.val = 1) (clear : KRKTenGeometry.Clear sk rs (1,2)) :
    rs.2.val = 4 ∨ rs.2.val = 5 := by
  have notThree : rs.2.val ≠ 3 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (0,3) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have mapped := KRKNineGeometry.frame_map g distinct
    (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  exact KRKNineMiddleLow.king_two_three_necessary sy sx rx mapped

private theorem low_second_eight_clear {rs : Square} (width : 4 ≤ rs.1.val) (row : rs.2.val = 1) :
    KRKEightGeometry.Clear (3,2) rs (2,0) := by
  have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
  refine ⟨Or.inl ?_,⟨((1 : Fin 8),0),?_⟩,?_⟩
  · dsimp [dInf,absDiff]; omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  · intro t guard
    have choices : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,row] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases choices with rfl | rfl
    · apply (KRKSevenNear.clear_iff distinct guard.2.1.symm guard.2.2.2).mpr
      refine Or.inr ⟨.high,rfl,Or.inr (Or.inr ⟨row,?_⟩)⟩
      omega
    · apply (KRKSevenMiddle.low_rook_clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide) (by decide)
        (by omega) distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm
        guard.2.2.1 guard.2.2.2).mpr
      exact ⟨rfl,Or.inl rfl⟩

private theorem low_edge_reply {sk rs : Square} {j : Fin 8} (sx : sk.1.val = 3) (sy : sk.2.val = 2)
    (rx : rs.1.val = 1) (height : rs.2.val = 4 ∨ rs.2.val = 5) (choice : j = 1 ∨ j = 2 ∨ j = 3)
    (guard : KRKCornerWeakBand.Guard sk rs (1,2) (0,j)) : KRKNineGeometry.Clear sk rs (0,j) := by
  have distinct : sk ≠ rs := by simp only [ne_iff_coords,sx,rx]; (try dsimp); omega
  let g := Frame.ofSym symSwap
  have mapped : KRKNineGeometry.Clear (g.f sk) (g.f rs) (g.f ((0 : Fin 8),j)) := by
    rcases choice with rfl | rfl | rfl
    · have apart : ((2 : Fin 8),2) ≠ g.f rs := by
        simp only [g,Frame.ofSym,symSwap,ne_iff_coords,rx]; dsimp; omega
      have eight := diagonal_near_eight_clear apart (Or.inl (by dsimp [g,Frame.ofSym,symSwap,dInf,absDiff]; omega))
      have region : KRKEightGlobal.Region (2,2) (g.f rs) (1,0) :=
        (KRKEightGlobal.edge_clear_iff apart (by decide)).mp eight
      apply KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) ?_ apart (by decide) region
      dsimp [g,Frame.ofSym,symSwap,dInf,absDiff]
      omega
    · have apart : ((3 : Fin 8),2) ≠ g.f rs := by
        simp only [g,Frame.ofSym,symSwap,ne_iff_coords,rx]; dsimp; omega
      have eight := low_second_eight_clear (rs := g.f rs) (by dsimp [g,Frame.ofSym,symSwap]; omega) rx
      have region : KRKEightGlobal.Region (3,2) (g.f rs) (2,0) :=
        (KRKEightGlobal.edge_clear_iff apart (by decide)).mp eight
      apply KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) ?_ apart (by decide) region
      dsimp [g,Frame.ofSym,symSwap,dInf,absDiff]
      omega
    · exact KRKNineMiddleLow.king_two_three_sufficient sy sx rx height
  have back := KRKNineGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
    (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega))) (g.ne_iff.mpr guard.2.1.symm)
    (by rw [g.distance]; exact guard.2.2.1) (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
  simpa only [Frame.inverse,g.left_inv] using back

def FileOne (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.1.val = 1 ∧ (rs.2.val = 4 ∨ rs.2.val = 5)

theorem file_one_clear {sk rs : Square} (region : FileOne sk rs) : KRKTenGeometry.Clear sk rs (1,2) := by
  obtain ⟨sx,sy,rx,height⟩ := region
  refine ⟨Or.inl ?_,⟨((0 : Fin 8),1),?_⟩,?_⟩
  · dsimp [dInf,absDiff]; omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  · intro t guard
    have choices : t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases choices with rfl | rfl | rfl
    · exact low_edge_reply sx sy rx height (Or.inl rfl) guard
    · exact low_edge_reply sx sy rx height (Or.inr (Or.inl rfl)) guard
    · exact low_edge_reply sx sy rx height (Or.inr (Or.inr rfl)) guard

theorem file_one_iff {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 2) (rx : rs.1.val = 1) :
    KRKTenGeometry.Clear sk rs (1,2) ↔ rs.2.val = 4 ∨ rs.2.val = 5 :=
  ⟨file_one_necessary distinct sx sy rx,fun height => file_one_clear ⟨sx,sy,rx,height⟩⟩

def Upper (sk rs : Square) : Prop :=
  sk.2.val = 4 ∧ rs.1.val = 2 ∧
    ((sk.1.val = 0 ∧ 4 ≤ rs.2.val) ∨ (sk.1.val = 1 ∧ 3 ≤ rs.2.val))

theorem upper_necessary {sk rs : Square} (distinct : sk ≠ rs) (sy : sk.2.val = 4)
    (sx : sk.1.val ≤ 2) (rx : rs.1.val = 2) (clear : KRKTenGeometry.Clear sk rs (1,2)) : Upper sk rs := by
  have safe := clear.1
  have height : 3 ≤ rs.2.val := by
    have options : rs.2.val = 0 ∨ 3 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    rcases options with zero | tall
    · have guard : KRKCornerWeakBand.Guard sk rs (1,2) (1,1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx,zero]
        simp <;> omega
      have next := clear.2.2 _ guard
      have rook : rs = ((2 : Fin 8),0) := Prod.ext (Fin.ext rx) (Fin.ext zero)
      rw [rook] at next
      exact False.elim (KRKNineInnerBoundary.rook_two_zero_high sy next)
    · exact tall
  have notTwo : sk.1.val ≠ 2 := by
    intro two
    by_cases three : rs.2.val = 3
    · have guard : KRKCornerWeakBand.Guard sk rs (1,2) (0,2) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,two,rx,three]
        simp <;> omega
      let g := Frame.ofSym symSwap
      have mapped := KRKNineGeometry.frame_map g distinct
        (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
        (clear.2.2 _ guard)
      have king : g.f sk = ((4 : Fin 8),2) := Prod.ext (Fin.ext sy) (Fin.ext two)
      have rook : g.f rs = ((3 : Fin 8),2) := Prod.ext (Fin.ext three) (Fin.ext rx)
      rw [king,rook] at mapped
      exact KRKNineSecondBoundary.no_nine mapped
    · have notFour : rs.2.val ≠ 4 := by
        intro four
        exact distinct (Prod.ext (Fin.ext (two.trans rx.symm)) (Fin.ext (sy.trans four.symm)))
      have guard : KRKCornerWeakBand.Guard sk rs (1,2) (2,1) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,two,rx]
        simp <;> omega
      exact no_lower_guard distinct (by dsimp [dInf,absDiff]; omega) clear guard
  refine ⟨sy,rx,?_⟩
  by_cases zero : sk.1.val = 0
  · refine Or.inl ⟨zero,?_⟩
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  · exact Or.inr ⟨by omega,height⟩

private theorem protected_high_no_clear {sk rs : Square} (sx : sk.1.val = 3) (high : 3 ≤ sk.2.val)
    (rx : rs.1.val = 2) (ry : rs.2.val = 3) : ¬KRKTenGeometry.Clear sk rs (1,2) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (1,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,rx,ry]
    simp <;> omega
  have next := clear.2.2 _ guard
  have rook : rs = ((2 : Fin 8),3) := Prod.ext (Fin.ext rx) (Fin.ext ry)
  rw [rook] at next
  exact KRKNineInnerBoundary.rook_two_three_right_high sx high next

def Region (sk rs : Square) : Prop :=
  KRKEightStrip.Region sk rs (1,2) ∨ RowThree sk rs ∨ FileOne sk rs ∨ Upper sk rs

theorem necessary {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKTenGeometry.Clear sk rs (1,2)) : Region sk rs := by
  rcases prison distinct far clear with ⟨sx,sy,ry⟩ | ⟨sy,sx,rx⟩ | ⟨sx,sy,rx⟩ | ⟨rx,ry⟩
  · rcases sy with sy | sy
    · have width : 3 ≤ rs.1.val := by have safe := clear.1; dsimp [SafeRook,dInf,absDiff] at safe; omega
      exact Or.inl ⟨rfl,rfl,sx,sy,ry,width⟩
    · have width : 2 ≤ rs.1.val := by have safe := clear.1; dsimp [SafeRook,dInf,absDiff] at safe; omega
      exact Or.inr (Or.inl ⟨sx,sy,ry,width⟩)
  · exact Or.inr (Or.inr (Or.inr (upper_necessary distinct sy sx rx clear)))
  · exact Or.inr (Or.inr (Or.inl ⟨sx,sy,rx,file_one_necessary distinct sx sy rx clear⟩))
  · have shape : sk.1.val = 3 ∨ sk.2.val = 4 := by
      have safe := clear.1
      dsimp [SafeRook,dInf,absDiff] at safe far
      omega
    rcases shape with sx | sy
    · by_cases two : sk.2.val = 2
      · exact Or.inr (Or.inl ⟨sx,two,ry,by omega⟩)
      · have high : 3 ≤ sk.2.val := by have safe := clear.1; dsimp [SafeRook,dInf,absDiff] at safe; omega
        exact False.elim (protected_high_no_clear sx high rx ry clear)
    · have width : sk.1.val ≤ 2 := by
        have safe := clear.1
        dsimp [SafeRook,dInf,absDiff] at safe
        by_cases three : sk.1.val = 3
        · exact False.elim (protected_high_no_clear three (by omega) rx ry clear)
        · omega
      exact Or.inr (Or.inr (Or.inr (upper_necessary distinct sy width rx clear)))

theorem upper_clear {sk rs : Square} (region : Upper sk rs) : KRKTenGeometry.Clear sk rs (1,2) := by
  obtain ⟨sy,rx,choices⟩ := region
  have file : sk.1.val = 0 ∨ sk.1.val = 1 := by omega
  have height : 3 ≤ rs.2.val := by omega
  have distinct : sk ≠ rs := by simp only [ne_iff_coords,rx]; omega
  have safe : SafeRook sk rs (1,2) := by dsimp [SafeRook,dInf,absDiff]; omega
  refine ⟨safe,⟨((0 : Fin 8),1),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
    simp <;> omega
  · intro t guard
    have targets : t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, j = 1 ∨ j = 2 → KRKCornerWeakBand.Guard sk rs (1,2) (0,j) →
        KRKNineGeometry.Clear sk rs (0,j) := by
      intro j choice guard
      let g := Frame.ofSym symSwap
      have mapped : KRKNineGeometry.Clear (g.f sk) (g.f rs) (g.f ((0 : Fin 8),j)) := by
        rcases choice with rfl | rfl
        · exact KRKNineUpperEntries.near_entry sy file height rx
        · exact KRKNineUpperEntries.second_entry sy file height rx
      have back := KRKNineGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega))) (g.ne_iff.mpr guard.2.1.symm)
        (by rw [g.distance]; exact guard.2.2.1) (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl
    · exact edge (Or.inl rfl) guard
    · exact edge (Or.inr rfl) guard
    · have apart : ((1 : Fin 8),3) ≠ rs := by simp only [ne_iff_coords,rx]; dsimp; omega
      have inner : KRKEightGlobal.Region (1,3) rs (1,1) := by
        change KRKEightInteriorExact.Region (1,3) rs (1,1)
        refine ⟨rfl,Or.inl ⟨rfl,Or.inr ?_⟩⟩
        exact ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl ⟨rx,by change 2 ≤ rs.2.val; omega⟩⟩)⟩
      apply KRKNineGeometry.king_step_clear (ns := ((1 : Fin 8),3)) ?_ apart (by decide) inner
      dsimp [dInf,absDiff]
      omega

private theorem old_clear {sk rs : Square} (region : KRKEightStrip.Region sk rs (1,2)) :
    KRKTenGeometry.Clear sk rs (1,2) := by
  have eight := KRKEightStrip.region_clear region
  have distinct : sk ≠ rs := by
    have shape := region
    dsimp [KRKEightStrip.Region] at shape
    simp only [ne_iff_coords]
    omega
  refine ⟨eight.1,eight.2.1,?_⟩
  intro t guard
  let q := krkPos .white sk rs t .white
  have notKing : sk ≠ t := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have material : IsKRK q .white sk rs t := ⟨distinct,notKing,guard.2.1.symm,rfl⟩
  have seven := (KRKSevenGeometry.kernel_seven_iff material rfl guard.2.2.1 guard.2.2.2).mpr (eight.2.2 t guard)
  exact (KRKNineGeometry.kernel_nine_iff material rfl guard.2.2.1 guard.2.2.2).mp (mateWithin_mono seven (by decide))

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTenGeometry.Clear sk rs (1,2) := by
  rcases region with old | row | file | upper
  · exact old_clear old
  · exact row_three_clear row
  · exact file_one_clear file
  · exact upper_clear upper

theorem clear_iff {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,2)) :
    KRKTenGeometry.Clear sk rs (1,2) ↔ Region sk rs := ⟨necessary distinct far,sufficient⟩

theorem kernel_ten_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2)) :
    MateWithin σ 10 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTenGeometry.kernel_ten_iff material turn notMate).trans (clear_iff material.1 far)

theorem kernel_exact_ten {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2)) :
    (MateWithin σ 10 q ∧ ¬MateWithin σ 9 q) ↔ Region sk rs ∧ ¬KRKEightStrip.Region sk rs (1,2) := by
  constructor
  · rintro ⟨ten,notNine⟩
    refine ⟨(kernel_ten_iff material turn far).mp ten,?_⟩
    intro old
    exact notNine (mateWithin_mono ((KRKEightNearStrip.kernel_eight_iff material turn far).mpr old) (by decide))
  · rintro ⟨region,notOld⟩
    refine ⟨(kernel_ten_iff material turn far).mpr region,?_⟩
    intro nine
    exact notOld ((KRKEightNearStrip.kernel_eight_iff material turn far).mp
      (KRKEightGeometry.weak_nine_eight material turn nine))

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),2))
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKTenGeometry.Clear sk rs wk ↔ Region (g.f sk) (g.f rs) := by
  have mappedFar : 2 ≤ dInf (g.f sk) (1,2) := by rw [←target,g.distance]; exact far
  constructor
  · intro clear
    have mapped := KRKTenGeometry.frame_map g distinct clear
    rw [target] at mapped
    exact necessary (g.ne_iff.mpr distinct) mappedFar mapped
  · intro region
    have mapped := sufficient region
    rw [←target] at mapped
    have back := KRKTenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct) mapped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKTenNearStrip
