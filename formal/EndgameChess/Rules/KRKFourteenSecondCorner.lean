import EndgameChess.Rules.KRKFourteenDeepStripHolding

namespace EndgameChess.Rules.KRKFourteenSecondCorner
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

def Prison (sk rs : Square) : Prop :=
  (sk.1.val = 4 ∧ 1 ≤ sk.2.val ∧ sk.2.val ≤ 3 ∧ rs.2.val = 3) ∨
  (sk.2.val = 4 ∧ 1 ≤ sk.1.val ∧ sk.1.val ≤ 3 ∧ rs.1.val = 3) ∨
  (sk.1.val = 4 ∧ (sk.2.val = 2 ∨ sk.2.val = 3) ∧ rs.1.val = 2) ∨
  (sk.2.val = 4 ∧ (sk.1.val = 2 ∨ sk.1.val = 3) ∧ rs.2.val = 2) ∨
  (sk.1.val = 4 ∧ sk.2.val = 4 ∧ rs.1.val = 3 ∧ rs.2.val = 3)

theorem prison {sk rs : Square} (far : 2 ≤ dInf sk (2,2))
    (clear : KRKFourteenGeometry.Clear sk rs (2,2)) : Prison sk rs := by
  have a := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (2,3)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have b := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (3,2)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have c := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (3,3)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have safe := clear.1
  clear clear
  dsimp at a b c
  dsimp [SafeRook,dInf,absDiff] at safe far
  dsimp [Prison]
  by_cases sx : sk.1.val = 4 <;> by_cases sy : sk.2.val = 4 <;>
    simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false] <;> omega

end EndgameChess.Rules.KRKFourteenSecondCorner
