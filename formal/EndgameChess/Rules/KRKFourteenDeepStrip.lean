import EndgameChess.Rules.KRKFourteenDeep

namespace EndgameChess.Rules.KRKFourteenDeepStrip
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Necessary depth-two near-corner families. Not yet a winning criterion. -/
def Prison (sk rs : Square) : Prop :=
  (sk.1.val = 4 ∧ (sk.2.val = 2 ∨ sk.2.val = 3) ∧ rs.2.val = 4) ∨
  (sk.1.val = 4 ∧ sk.2.val = 3 ∧ rs.1.val = 2) ∨
  (sk.1.val = 4 ∧ (sk.2.val = 4 ∨ sk.2.val = 5) ∧ rs.1.val = 3 ∧ rs.2.val = 4) ∨
  (sk.2.val = 5 ∧ 1 ≤ sk.1.val ∧ sk.1.val ≤ 3 ∧ rs.1.val = 3)

theorem prison {sk rs : Square} (far : 2 ≤ dInf sk (2,3))
    (clear : KRKFourteenGeometry.Clear sk rs (2,3)) : Prison sk rs := by
  have a := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (2,4)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have b := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (3,2)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have c := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (3,3)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have d := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (3,4)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have safe := clear.1
  clear clear
  dsimp at a b c d
  dsimp [SafeRook,dInf,absDiff] at safe far
  dsimp [Prison]
  by_cases file : rs.1.val = 3 <;> by_cases row : rs.2.val = 4 <;>
    simp_all only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false] <;> omega

end EndgameChess.Rules.KRKFourteenDeepStrip
