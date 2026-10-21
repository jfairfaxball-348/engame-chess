import EndgameChess.Rules.KRKBox.Phase

namespace EndgameChess.Rules
open EndgameChess.KK

/-- Both actual endpoint widths of the guarded phase pay its worst-case eight
board plies with large-side excess. This is not a mating-distance theorem. -/
theorem krk_guarded_large_box_cost {a b : Nat} (ha : 1 ≤ a) (ha2 : a ≤ 2) :
    (8 + 8*boxExcess (6-a) (7-b) ≤ 8*boxExcess (7-a) (7-b)) ∧
    (8 + 8*boxExcess (a+1) (7-b) ≤ 8*boxExcess (7-a) (7-b)) := by
  simp only [boxExcess]
  omega

end EndgameChess.Rules
