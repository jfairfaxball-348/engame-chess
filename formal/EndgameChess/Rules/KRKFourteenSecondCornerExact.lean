import EndgameChess.Rules.KRKFourteenSecondCornerBounds

namespace EndgameChess.Rules.KRKFourteenSecondCornerExact
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Horizontal (sk rs : Square) : Prop := sk.1.val = 4 ∧ rs.2.val = 3 ∧
  ((sk.2.val = 1 ∧ 4 ≤ rs.1.val) ∨ (sk.2.val = 2 ∧ 3 ≤ rs.1.val))

def Region (sk rs : Square) : Prop := Horizontal sk rs ∨ Horizontal (symSwap.f sk) (symSwap.f rs)

private theorem high_row_no_clear {r : Fin 8} (apart : ((4,3) : Square) ≠ (r,3)) :
    ¬KRKFourteenGeometry.Clear (4,3) (r,3) (2,2) := by
  intro clear
  by_cases zero : r = 0
  · rw [zero] at clear
    have guard : KRKCornerWeakBand.Guard ((4 : Fin 8),3) (0,3) (2,2) (1,2) := by
      dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    exact KRKFourteenSecondCornerBounds.near_four_zero_no_thirteen (clear.2.2 _ guard)
  by_cases three : r = 3
  · rw [three] at clear
    have guard : KRKCornerWeakBand.Guard ((4 : Fin 8),3) (3,3) (2,2) (2,1) := by
      dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
    have mapped := KRKThirteenGeometry.frame_map (Frame.ofSym symSwap) (by decide) (by decide) (by decide)
      (by decide) (by dsimp [RookSees,RookLine,OnSeg]; decide) (clear.2.2 _ guard)
    exact KRKFourteenSecondCornerBounds.near_three_four_no_thirteen mapped
  have high : 5 ≤ r.val := by
    have safe := clear.1
    have notFour : r.val ≠ 4 := by intro eq; exact apart (Prod.ext (Fin.ext eq.symm) rfl)
    have notZero : r.val ≠ 0 := fun eq => zero (Fin.ext eq)
    have notThree : r.val ≠ 3 := fun eq => three (Fin.ext eq)
    dsimp [SafeRook,dInf,absDiff] at safe
    simp only [show ((3 : Fin 8).val) = 3 from rfl,show ((4 : Fin 8).val) = 4 from rfl] at safe
    omega
  have guard : KRKCornerWeakBand.Guard ((4 : Fin 8),3) (r,3) (2,2) (1,3) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp
    simp only [show ((3 : Fin 8).val) = 3 from rfl,show ((4 : Fin 8).val) = 4 from rfl]
    simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]
    omega
  exact KRKFourteenSecondCornerBounds.central_four_three_no_thirteen (clear.2.2 _ guard)

private theorem row_necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 4)
    (low : 1 ≤ sk.2.val) (high : sk.2.val ≤ 3) (ry : rs.2.val = 3)
    (clear : KRKFourteenGeometry.Clear sk rs (2,2)) : Horizontal sk rs := by
  have notHigh : sk.2.val ≠ 3 := by
    intro sy
    have kingEq : sk = ((4 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = (rs.1,(3 : Fin 8)) := Prod.ext rfl (Fin.ext ry)
    rw [kingEq,rookEq] at apart clear
    exact high_row_no_clear apart clear
  have notZero : rs.1.val ≠ 0 := by
    intro zero
    have guard : KRKCornerWeakBand.Guard sk rs (2,2) (1,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry,zero]
      dsimp; omega
    have kingEq : sk = ((4 : Fin 8),sk.2) := Prod.ext (Fin.ext sx) rfl
    have rookEq : rs = ((0 : Fin 8),3) := Prod.ext (Fin.ext zero) (Fin.ext ry)
    have child := clear.2.2 _ guard
    rw [kingEq,rookEq] at child
    exact KRKFourteenSecondCornerBounds.near_four_zero_no_thirteen child
  have safe := clear.1
  dsimp [SafeRook,dInf,absDiff] at safe
  dsimp [Horizontal]
  omega

private theorem file_two_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 4)
    (ys : sk.2.val = 2 ∨ sk.2.val = 3) (rx : rs.1.val = 2) : ¬KRKFourteenGeometry.Clear sk rs (2,2) := by
  intro clear
  have safe := clear.1
  have away : rs.2.val = 0 ∨ 4 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
  rcases ys with two | three
  · have guard : KRKCornerWeakBand.Guard sk rs (2,2) (1,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,two,rx]
      dsimp; omega
    have kingEq : sk = ((4 : Fin 8),2) := Prod.ext (Fin.ext sx) (Fin.ext two)
    have child := clear.2.2 _ guard
    rw [kingEq] at child
    exact KRKFourteenSecondCornerBounds.near_four_two_file_two_no_thirteen rx (by omega) child
  · have guard : KRKCornerWeakBand.Guard sk rs (2,2) (3,1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,three,rx]
      dsimp; omega
    have kingEq : sk = ((4 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext three)
    have rookEq : rs = ((2 : Fin 8),rs.2) := Prod.ext (Fin.ext rx) rfl
    have child := clear.2.2 _ guard
    let g := Frame.ofSym symSwap
    have mapped := KRKThirteenGeometry.frame_map g apart
      (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2 child
    rw [kingEq,rookEq] at mapped
    exact KRKFourteenSecondCornerBounds.central_three_four_no_thirteen mapped

private theorem diagonal_no_clear : ¬KRKFourteenGeometry.Clear ((4 : Fin 8),4) (3,3) (2,2) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard ((4 : Fin 8),4) (3,3) (2,2) (1,1) := by
    dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]; decide
  exact KRKFourteenSecondCornerBounds.inner_diagonal_no_thirteen (clear.2.2 _ guard)

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (2,2))
    (clear : KRKFourteenGeometry.Clear sk rs (2,2)) : Region sk rs := by
  have mapped := KRKFourteenGeometry.frame_map (Frame.ofSym symSwap) apart clear
  have mappedApart := (Frame.ofSym symSwap).ne_iff.mpr apart
  rcases KRKFourteenSecondCorner.prison far clear with
    ⟨sx,low,high,ry⟩ | ⟨sy,low,high,rx⟩ | ⟨sx,ys,rx⟩ | ⟨sy,xs,ry⟩ | ⟨sx,sy,rx,ry⟩
  · exact Or.inl (row_necessary apart sx low high ry clear)
  · exact Or.inr (row_necessary mappedApart sy low high rx mapped)
  · exact False.elim (file_two_no_clear apart sx ys rx clear)
  · exact False.elim (file_two_no_clear mappedApart sy xs ry mapped)
  · have kingEq : sk = ((4 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = ((3 : Fin 8),3) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    rw [kingEq,rookEq] at clear
    exact False.elim (diagonal_no_clear clear)

private theorem old_subset {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (2,2))
    (clear : KRKTwelveGeometry.Clear sk rs (2,2)) : KRKFourteenGeometry.Clear sk rs (2,2) := by
  have notRook : rs ≠ ((2 : Fin 8),2) := by
    intro equal
    have safe := clear.1
    rw [equal] at safe
    dsimp [SafeRook,dInf,absDiff] at safe far
    omega
  let q := krkPos .white sk rs (2,2) .black
  have material : IsKRK q .white sk rs (2,2) := ⟨apart,ne_of_dInf_pos (by omega),notRook,rfl⟩
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material rfl far).mp mate)
    change 2 = 0 at zero
    contradiction
  exact (KRKFourteenGeometry.kernel_fourteen_iff material rfl notMate).mp
    (mateWithin_mono ((KRKTwelveGeometry.kernel_twelve_iff material rfl notMate).mpr clear) (by decide))

private theorem horizontal_sufficient {sk rs : Square} (apart : sk ≠ rs) (region : Horizontal sk rs) :
    KRKFourteenGeometry.Clear sk rs (2,2) := by
  obtain ⟨sx,ry,⟨sy,rx⟩ | ⟨sy,rx⟩⟩ := region
  · have old : KRKTwelveSecondCorner.Region sk rs := Or.inl ⟨sx,sy,ry,rx⟩
    have far : 2 ≤ dInf sk (2,2) := by dsimp [dInf,absDiff]; omega
    exact old_subset apart far (KRKTwelveSecondCorner.sufficient old)
  · have kingEq : sk = ((4 : Fin 8),2) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = (rs.1,(3 : Fin 8)) := Prod.ext rfl (Fin.ext ry)
    rw [kingEq,rookEq]
    exact KRKFourteenSecondCornerEntries.opposition_clear rx

theorem sufficient {sk rs : Square} (apart : sk ≠ rs) (region : Region sk rs) : KRKFourteenGeometry.Clear sk rs (2,2) := by
  rcases region with horizontal | vertical
  · exact horizontal_sufficient apart horizontal
  · have source := horizontal_sufficient ((Frame.ofSym symSwap).ne_iff.mpr apart) vertical
    have mapped := KRKFourteenGeometry.frame_map (Frame.ofSym symSwap) ((Frame.ofSym symSwap).ne_iff.mpr apart) source
    simpa only [Frame.ofSym,symSwap.invol,show symSwap.f ((2 : Fin 8),2) = ((2 : Fin 8),2) from rfl] using mapped

theorem kernel_fourteen_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (2,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (2,2)) :
    MateWithin σ 14 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 2 = 0 at zero
    contradiction
  exact (KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).trans ⟨necessary material.1 far,sufficient material.1⟩

theorem kernel_exact_fourteen {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (2,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (2,2)) :
    (MateWithin σ 14 q ∧ ¬MateWithin σ 13 q) ↔ Region sk rs ∧ ¬KRKTwelveSecondCorner.Region sk rs := by
  have earlier : MateWithin σ 12 q ↔ KRKTwelveSecondCorner.Region sk rs := by
    have global := KRKTwelveGlobal.kernel_twelve_iff material turn far
    have notTerminal : ¬KRKMateGeometry.Terminal sk rs (2,2) := by
      intro t
      have zero := KRKEdgeDepth.terminal_depth_zero t
      change 2 = 0 at zero
      contradiction
    exact (global.trans (or_iff_right notTerminal)).trans KRKThirteenInteriorBarriers.second_region_iff
  constructor
  · rintro ⟨fourteen,notThirteen⟩
    exact ⟨(kernel_fourteen_iff material turn far).mp fourteen,fun old => notThirteen (mateWithin_mono (earlier.mpr old) (by decide))⟩
  · rintro ⟨region,notOld⟩
    exact ⟨(kernel_fourteen_iff material turn far).mpr region,fun thirteen =>
      notOld (earlier.mp (KRKTwelveGeometry.weak_thirteen_twelve material turn thirteen))⟩

end EndgameChess.Rules.KRKFourteenSecondCornerExact
