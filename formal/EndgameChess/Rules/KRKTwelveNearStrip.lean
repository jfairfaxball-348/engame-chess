import EndgameChess.Rules.KRKTwelveCentralExact
import EndgameChess.Rules.KRKElevenInner

namespace EndgameChess.Rules.KRKTwelveNearStrip
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Necessary covering reduction only; the lower near-strip reply is
retained because it can now enter a genuine eleven-ply near-strip win. -/
def Prison (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ (sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3) ∧ rs.2.val = 3) ∨
  (sk.1.val = 3 ∧ (sk.2.val = 2 ∨ sk.2.val = 3) ∧ rs.1.val = 1) ∨
  (sk.2.val = 4 ∧ sk.1.val ≤ 2 ∧ rs.1.val = 2) ∨
  (sk.2.val = 4 ∧ (sk.1.val = 1 ∨ sk.1.val = 2) ∧ rs.2.val = 2) ∨
  (sk.1.val = 3 ∧ sk.2.val = 4 ∧ rs.1.val = 2 ∧ rs.2.val = 3)

theorem prison {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKTwelveGeometry.Clear sk rs (1,2)) : Prison sk rs := by
  have a := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered apart clear (t := (1,3)) (by decide)
    (Or.inr (Or.inl ⟨Or.inl rfl,by decide,by decide⟩)))
  have b := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered apart clear (t := (2,2)) (by decide) (Or.inl (by decide)))
  have c := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered apart clear (t := (2,3)) (by decide) (Or.inl (by decide)))
  have safe := clear.1
  clear clear
  dsimp at a b c
  have kingFar : 3 ≤ sk.1.val ∨ sk.2.val = 0 ∨ 4 ≤ sk.2.val := by
    dsimp [dInf,absDiff] at far
    omega
  have protection : 3 ≤ rs.1.val ∨ rs.2.val = 0 ∨ 4 ≤ rs.2.val ∨
      (sk.1.val ≤ rs.1.val + 1 ∧ rs.1.val ≤ sk.1.val + 1 ∧
       sk.2.val ≤ rs.2.val + 1 ∧ rs.2.val ≤ sk.2.val + 1) := by
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  clear safe far
  dsimp [Prison]
  by_cases one : rs.1.val = 1 <;> by_cases two : rs.1.val = 2 <;>
    by_cases rowTwo : rs.2.val = 2 <;> by_cases rowThree : rs.2.val = 3 <;>
    simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false] <;> omega

theorem row_two_necessary {sk rs : Square} (apart : sk ≠ rs) (sy : sk.2.val = 4)
    (sx : sk.1.val = 1 ∨ sk.1.val = 2) (ry : rs.2.val = 2) (rx : 3 ≤ rs.1.val)
    (clear : KRKTwelveGeometry.Clear sk rs (1,2)) : rs.1.val = 3 := by
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (2,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,ry]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have evaluated := (KRKElevenNearStrip.clear_iff (g.ne_iff.mpr apart) (g.ne_iff.mpr guard.2.1.symm)).mp mapped
  rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
  · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,g,Frame.ofSym,symSwap,dInf,absDiff] at distance shape <;> omega
  · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;>
      dsimp [g,Frame.ofSym,symSwap] at equal <;> omega

private theorem inner_three_four_two_three : ¬KRKElevenInner.Eleven ((3 : Fin 8),4) ((2 : Fin 8),3) := by
  rintro ((⟨i,entry⟩ | ⟨i,entry⟩) | (⟨i,equal,_⟩ | ⟨i,equal,_⟩))
  all_goals cases i <;>
    dsimp [KRKElevenInner.KingEntry,KRKElevenInner.king,symSwap,dInf,absDiff] at * <;>
    simp only [ne_iff_coords,square_eq_iff,Fin.ext_iff] at * <;> (try dsimp at *) <;> first | omega | simp_all

private theorem inner_three_three_two_three : ¬KRKElevenInner.Eleven ((3 : Fin 8),3) ((2 : Fin 8),3) := by
  rintro ((⟨i,entry⟩ | ⟨i,entry⟩) | (⟨i,equal,_⟩ | ⟨i,equal,_⟩))
  all_goals cases i <;>
    dsimp [KRKElevenInner.KingEntry,KRKElevenInner.king,KRKTenInner.Region,KRKTenInner.Horizontal,
      KRKEightInner.Horizontal,KRKTenInner.SideExtra,KRKTenInner.HighExtra,
      KRKNineNearStrip.RookCondition,symSwap,dInf,absDiff] at * <;>
    simp only [ne_iff_coords,square_eq_iff,Fin.ext_iff] at * <;> (try dsimp at *) <;> omega

theorem protected_high_no_clear : ¬KRKTwelveGeometry.Clear ((3 : Fin 8),4) ((2 : Fin 8),3) (1,2) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),4) ((2 : Fin 8),3) (1,2) (1,1) := by
    dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
    decide
  have evaluated := (KRKElevenInner.clear_iff (by decide) (by decide) (by decide)
    guard.2.2.1 guard.2.2.2).mp (clear.2.2 _ guard)
  exact inner_three_four_two_three evaluated

theorem row_three_high_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 3) (ry : rs.2.val = 3) : ¬KRKTwelveGeometry.Clear sk rs (1,2) := by
  intro clear
  have kingEq : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
  subst sk
  have notThree : rs.1.val ≠ 3 := by
    simp only [ne_iff_coords] at apart
    (try dsimp at apart)
    omega
  by_cases two : rs.1.val = 2
  · have rookEq : rs = ((2 : Fin 8),3) := Prod.ext (Fin.ext two) (Fin.ext ry)
    rw [rookEq] at clear
    have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),3) ((2 : Fin 8),3) (1,2) (1,1) := by
      dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    exact inner_three_three_two_three ((KRKElevenInner.clear_iff (by decide) (by decide) (by decide)
      guard.2.2.1 guard.2.2.2).mp (clear.2.2 _ guard))
  · have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),3) rs (1,2) (2,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
      simp <;> omega
    let g := Frame.ofSym symSwap
    have mapped := KRKElevenGeometry.frame_map g apart (by decide) guard.2.1.symm guard.2.2.1 guard.2.2.2
      (clear.2.2 _ guard)
    have evaluated := (KRKElevenNearStrip.clear_iff (g.ne_iff.mpr apart) (g.ne_iff.mpr guard.2.1.symm)).mp mapped
    rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
    · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,g,Frame.ofSym,symSwap,dInf,absDiff] at distance shape <;> omega
    · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;>
        dsimp [g,Frame.ofSym,symSwap] at equal <;> omega

theorem row_three_necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3) (ry : rs.2.val = 3)
    (clear : KRKTwelveGeometry.Clear sk rs (1,2)) :
    KRKEightStrip.Region sk rs (1,2) ∨ KRKTenNearStrip.RowThree sk rs := by
  have notHigh : sk.2.val ≠ 3 := fun high => row_three_high_no_clear apart sx high ry clear
  have safe := clear.1
  dsimp [SafeRook,dInf,absDiff] at safe
  dsimp [KRKEightStrip.Region,KRKTenNearStrip.RowThree]
  omega

private theorem no_ten_inner_two_zero {sk : Square} : ¬KRKTenInner.Region sk ((2 : Fin 8),0) := by
  dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
    KRKTenInner.SideExtra,KRKTenInner.HighExtra,KRKNineNearStrip.RookCondition,symSwap]
  omega

theorem upper_low_no_clear {sk rs : Square} (apart : sk ≠ rs) (sy : sk.2.val = 4)
    (sx : sk.1.val ≤ 2) (rx : rs.1.val = 2) (ry : rs.2.val = 0) :
    ¬KRKTwelveGeometry.Clear sk rs (1,2) := by
  intro clear
  have rookEq : rs = ((2 : Fin 8),0) := Prod.ext (Fin.ext rx) (Fin.ext ry)
  rw [rookEq] at clear apart
  have guard : KRKCornerWeakBand.Guard sk ((2 : Fin 8),0) (1,2) (1,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy]
    simp <;> omega
  have evaluated := (KRKElevenInner.clear_iff apart (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
    (by decide) guard.2.2.1 guard.2.2.2).mp (clear.2.2 _ guard)
  rcases evaluated with (⟨i,_,_,region⟩ | ⟨i,_,_,region⟩) | (⟨i,equal,_⟩ | ⟨i,equal,_⟩)
  · exact no_ten_inner_two_zero region
  · exact no_ten_inner_two_zero region
  all_goals cases i <;> simp only [KRKElevenInner.king,square_eq_iff,Fin.ext_iff] at equal <;>
    dsimp [symSwap] at equal <;> omega

end EndgameChess.Rules.KRKTwelveNearStrip
