import EndgameChess.Rules.KRKFourteenCentralBounds

namespace EndgameChess.Rules.KRKFourteenCentralNecessary
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Opposition (sk rs : Square) : Prop := sk.1.val = 3 ∧ sk.2.val = 4 ∧ rs.2.val = 2 ∧ 3 ≤ rs.1.val

def Upper (sk rs : Square) : Prop := sk.2.val = 5 ∧ rs.1.val = 2 ∧
  ((sk.1.val = 0 ∧ 5 ≤ rs.2.val) ∨ (sk.1.val = 1 ∧ 4 ≤ rs.2.val) ∨ (sk.1.val = 2 ∧ rs.2.val = 4))

def Region (sk rs : Square) : Prop := KRKTwelveCentralExact.Region sk rs ∨ Opposition sk rs ∨ Upper sk rs

private theorem second_rook_line {rs : Square} (clear : KRKFourteenGeometry.Clear (3,4) rs (1,3)) :
    RookLine rs ((2 : Fin 8),2) := by
  by_cases line : RookLine rs ((2 : Fin 8),2)
  · exact line
  have notRook : ((2 : Fin 8),2) ≠ rs := by
    intro equal
    have safe := clear.1
    rw [←equal] at safe
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),4) rs (1,3) (2,2) :=
    ⟨by decide,notRook,by decide,fun h => line h.1⟩
  exact False.elim (KRKFourteenCentralBounds.second_three_four_no_thirteen (clear.2.2 _ guard))

private theorem upper_opposition_necessary {sk rs : Square} (sx : sk.1.val = 3) (sy : sk.2.val = 4)
    (condition : rs.1.val = 1 ∨ rs.2.val ≤ 2 ∨ 6 ≤ rs.2.val)
    (clear : KRKFourteenGeometry.Clear sk rs (1,3)) : Opposition sk rs := by
  have kingEq : sk = ((3 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext sy)
  have source := clear
  rw [kingEq] at source
  have line := (second_rook_line source).2
  dsimp at line
  by_cases row : rs.2.val = 2
  · have width : 3 ≤ rs.1.val := by
      have safe := clear.1
      dsimp [SafeRook,dInf,absDiff] at safe
      omega
    exact ⟨sx,sy,row,width⟩
  · have file : rs.1.val = 2 := by omega
    have notThree : rs.2.val ≠ 3 := by omega
    have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),4) rs (1,3) (1,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,file]
      dsimp; omega
    exact False.elim (KRKFourteenCentralBounds.near_three_four_file_two_no_thirteen file notThree (source.2.2 _ guard))

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKFourteenGeometry.Clear sk rs (1,3)) : Region sk rs := by
  have safe := clear.1
  rcases KRKFourteenCentralPrison.prison apart far clear with legal | row | file | upper
  · rcases legal with ⟨king,ry,width⟩ | ⟨sx,sy,rx,height⟩ | ⟨sx,sy,condition⟩
    · have shape : (sk.1.val = 3 ∧ sk.2.val = 4) ∨ sk.2.val = 5 := by
        rcases king with low | high
        · exact Or.inl low
        · exact Or.inr high.1
      have guard : KRKCornerWeakBand.Guard sk rs (1,3) (2,2) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,ry]
        dsimp; rcases shape with low | high <;> omega
      exact False.elim (KRKFourteenCentralBounds.second_upper_row_no_thirteen shape ry (clear.2.2 _ guard))
    · have oldHeight : rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val := by
        dsimp [SafeRook,dInf,absDiff] at safe
        omega
      exact Or.inl (Or.inr (Or.inr ⟨sx,sy,rx,oldHeight⟩))
    · exact Or.inr (Or.inl (upper_opposition_necessary sx sy condition clear))
  · obtain ⟨sx,low,high,ry⟩ := row
    have ys : sk.2.val = 2 ∨ sk.2.val = 3 ∨ sk.2.val = 4 := by omega
    rcases ys with two | three | four
    · have width : 3 ≤ rs.1.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
      exact Or.inl (Or.inl ⟨sx,two,ry,width⟩)
    · have notOne : rs.1.val ≠ 1 := by dsimp [SafeRook,dInf,absDiff] at safe; omega
      have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,three,ry]
        dsimp; omega
      have kingEq : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext three)
      have rookEq : rs = (rs.1,(4 : Fin 8)) := Prod.ext rfl (Fin.ext ry)
      have child := clear.2.2 _ guard
      rw [kingEq,rookEq] at child
      exact False.elim (KRKFourteenCentralBounds.near_three_three_row_four_no_thirteen
        (fun h => notOne (congrArg Fin.val h)) child)
    · have kingEq : sk = ((3 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext four)
      have source := clear
      rw [kingEq] at source
      have line := (second_rook_line source).2
      have rx : rs.1.val = 2 := by dsimp at line; omega
      have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),4) rs (1,3) (1,2) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx,ry]
        dsimp; omega
      exact False.elim (KRKFourteenCentralBounds.near_three_four_file_two_no_thirteen rx (by omega) (source.2.2 _ guard))
  · obtain ⟨sx,ys,rx⟩ := file
    have height : rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    rcases ys with three | four
    · exact Or.inl (Or.inr (Or.inr ⟨sx,three,rx,height⟩))
    · have kingEq : sk = ((3 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext four)
      rw [kingEq] at clear
      have line := (second_rook_line clear).2
      dsimp at line
      omega
  · obtain ⟨sy,sx,rx⟩ := upper
    have height : 4 ≤ rs.2.val := by
      by_cases high : 4 ≤ rs.2.val
      · exact high
      have low : rs.2.val ≤ 1 := by dsimp [SafeRook,dInf,absDiff] at safe; omega
      have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
        dsimp; omega
      have kingEq : sk = (sk.1,(5 : Fin 8)) := Prod.ext rfl (Fin.ext sy)
      have child := clear.2.2 _ guard
      rw [kingEq] at child
      exact False.elim (KRKFourteenCentralBounds.near_upper_low_rook_no_thirteen rx low child)
    have slots : sk.1.val = 0 ∨ sk.1.val = 1 ∨ sk.1.val = 2 ∨ sk.1.val = 3 := by omega
    rcases slots with zero | one | two | three
    · have high : 5 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
      exact Or.inr (Or.inr ⟨sy,rx,Or.inl ⟨zero,high⟩⟩)
    · exact Or.inr (Or.inr ⟨sy,rx,Or.inr (Or.inl ⟨one,height⟩)⟩)
    · have kingEq : sk = ((2 : Fin 8),5) := Prod.ext (Fin.ext two) (Fin.ext sy)
      have rookEq : rs = ((2 : Fin 8),rs.2) := Prod.ext (Fin.ext rx) rfl
      have notFive : rs.2.val ≠ 5 := by
        simp only [ne_iff_coords] at apart
        omega
      have notHigh : ¬6 ≤ rs.2.val := by
        intro high
        rw [kingEq,rookEq] at clear
        exact KRKFourteenCentralBounds.upper_two_above_no_clear high clear
      exact Or.inr (Or.inr ⟨sy,rx,Or.inr (Or.inr ⟨two,by omega⟩)⟩)
    · have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
        dsimp; omega
      have kingEq : sk = ((3 : Fin 8),5) := Prod.ext (Fin.ext three) (Fin.ext sy)
      have child := clear.2.2 _ guard
      rw [kingEq] at child
      exact False.elim (KRKFourteenCentralBounds.near_upper_three_high_no_thirteen rx height child)

end EndgameChess.Rules.KRKFourteenCentralNecessary
