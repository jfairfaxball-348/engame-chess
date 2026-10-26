import EndgameChess.Rules.KRKThreePly

namespace EndgameChess.Rules.KRKThreePly
open EndgameChess.KK KRKMateGeometry KRKImmediate KRKLastReply
set_option maxHeartbeats 500000

def CoordinateStep (sk : Square) (x y : Nat) : Prop :=
  max (absDiff sk.1.val x) (absDiff sk.2.val y) = 1

/-- The central-edge three-ply region with every landing-coordinate
quantifier eliminated. The last two rows are complete rook-ray tests. -/
def MiddleThree (sk rs wk : Square) : Prop :=
  (sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ rs.2.val ≠ 0 ∧
    2 ≤ absDiff rs.1.val wk.1.val) ∨
  (2 ≤ rs.2.val ∧ rs.1.val + 1 = wk.1.val ∧ CoordinateStep sk (wk.1.val + 1) 2) ∨
  (2 ≤ rs.2.val ∧ rs.1.val = wk.1.val + 1 ∧ CoordinateStep sk (wk.1.val - 1) 2) ∨
  (sk.1.val = wk.1.val + 1 ∧ sk.2.val = 2 ∧
    (rs.1.val + 1 = wk.1.val ∨ 3 ≤ rs.2.val ∨
      (rs.2.val = 2 ∧ rs.1.val < sk.1.val))) ∨
  (sk.1.val + 1 = wk.1.val ∧ sk.2.val = 2 ∧
    (rs.1.val = wk.1.val + 1 ∨ 3 ≤ rs.2.val ∨
      (rs.2.val = 2 ∧ sk.1.val < rs.1.val)))

theorem last_middle_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) :
    LastReply sk rs wk ↔ sk.2.val = 2 ∧ 2 ≤ rs.2.val ∧
      ((sk.1.val = wk.1.val + 1 ∧ rs.1.val + 1 = wk.1.val) ∨
       (sk.1.val + 1 = wk.1.val ∧ rs.1.val = wk.1.val + 1)) := by
  simp [LastReply, HorizontalLast, SafeRook, dInf, absDiff, rank]
  omega

theorem immediate_middle_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) :
    MateNow sk rs wk ↔ sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ rs.2.val ≠ 0 ∧
      2 ≤ absDiff rs.1.val wk.1.val := by
  simp [MateNow, Horizontal, rankTarget, fileTarget, RookSees, RookLine, OnSeg, absDiff, rank]
  omega

theorem king_entry_middle_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) :
    KingEntry sk rs wk ↔
      (2 ≤ rs.2.val ∧ rs.1.val + 1 = wk.1.val ∧ CoordinateStep sk (wk.1.val + 1) 2) ∨
      (2 ≤ rs.2.val ∧ rs.1.val = wk.1.val + 1 ∧ CoordinateStep sk (wk.1.val - 1) 2) := by
  constructor
  · rintro ⟨t, distance, _, _, last⟩
    obtain ⟨ty, ry, right | left⟩ := (last_middle_iff rank low high).mp last
    · refine Or.inl ⟨ry, right.2, ?_⟩
      simpa only [CoordinateStep, dInf, right.1, ty] using distance
    · refine Or.inr ⟨ry, left.2, ?_⟩
      have tx : t.1.val = wk.1.val - 1 := by omega
      simpa only [CoordinateStep, dInf, tx, ty] using distance
  · rintro (⟨ry, rx, distance⟩ | ⟨ry, rx, distance⟩)
    · let t : Square := (⟨wk.1.val + 1, by omega⟩, (2 : Fin 8))
      refine ⟨t, ?_, ?_, ?_, (last_middle_iff rank low high).mpr ?_⟩
      · exact distance
      · simp only [ne_iff_coords]; dsimp [t]; omega
      · simp [dInf, absDiff, t, rank] <;> omega
      · exact ⟨rfl, ry, Or.inl ⟨rfl, rx⟩⟩
    · let t : Square := (⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩, (2 : Fin 8))
      refine ⟨t, ?_, ?_, ?_, (last_middle_iff rank low high).mpr ?_⟩
      · exact distance
      · simp only [ne_iff_coords]; dsimp [t]; omega
      · simp [dInf, absDiff, t, rank] <;> omega
      · refine ⟨rfl, ry, Or.inr ⟨?_, rx⟩⟩
        dsimp [t]; omega

theorem rook_entry_middle_iff {sk rs wk : Square} (distinct : sk ≠ rs)
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) :
    RookEntry sk rs wk ↔
      (sk.1.val = wk.1.val + 1 ∧ sk.2.val = 2 ∧
        (rs.1.val + 1 = wk.1.val ∨ 3 ≤ rs.2.val ∨
          (rs.2.val = 2 ∧ rs.1.val < sk.1.val))) ∨
      (sk.1.val + 1 = wk.1.val ∧ sk.2.val = 2 ∧
        (rs.1.val = wk.1.val + 1 ∨ 3 ≤ rs.2.val ∨
          (rs.2.val = 2 ∧ sk.1.val < rs.1.val))) := by
  constructor
  · rintro ⟨t, sees, _, _, last⟩
    simp only [ne_iff_coords] at distinct
    obtain ⟨sy, ty, right | left⟩ := (last_middle_iff rank low high).mp last
    · refine Or.inl ⟨right.1, sy, ?_⟩
      simp only [RookSees, RookLine, OnSeg] at sees
      omega
    · refine Or.inr ⟨left.1, sy, ?_⟩
      simp only [RookSees, RookLine, OnSeg] at sees
      omega
  · rintro (⟨sx, sy, ray⟩ | ⟨sx, sy, ray⟩)
    · by_cases sourceFile : rs.1.val + 1 = wk.1.val
      · let t : Square := (rs.1, if rs.2.val = 7 then (6 : Fin 8) else (7 : Fin 8))
        have tf : t.1.val = rs.1.val := rfl
        have ty : 2 ≤ t.2.val := by dsimp [t]; split <;> decide
        have changed : rs.2.val ≠ t.2.val := by
          dsimp [t]; split
          · change rs.2.val ≠ 6; omega
          · change rs.2.val ≠ 7; assumption
        refine ⟨t, ?_, ?_, ?_, (last_middle_iff rank low high).mpr ⟨sy, ty, Or.inl ⟨sx, by omega⟩⟩⟩
        · simp only [RookSees, RookLine, OnSeg]; omega
        · rw [ne_iff_coords]; omega
        · rw [ne_iff_coords]; omega
      · let t : Square := (⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩, rs.2)
        have tf : t.1.val + 1 = wk.1.val := by dsimp [t]; omega
        have ty : t.2.val = rs.2.val := rfl
        have tall : 2 ≤ t.2.val := by omega
        refine ⟨t, ?_, ?_, ?_, (last_middle_iff rank low high).mpr ⟨sy, tall, Or.inl ⟨sx, tf⟩⟩⟩
        · simp only [RookSees, RookLine, OnSeg]; omega
        · rw [ne_iff_coords]; omega
        · rw [ne_iff_coords]; omega
    · by_cases sourceFile : rs.1.val = wk.1.val + 1
      · let t : Square := (rs.1, if rs.2.val = 7 then (6 : Fin 8) else (7 : Fin 8))
        have tf : t.1.val = rs.1.val := rfl
        have ty : 2 ≤ t.2.val := by dsimp [t]; split <;> decide
        have changed : rs.2.val ≠ t.2.val := by
          dsimp [t]; split
          · change rs.2.val ≠ 6; omega
          · change rs.2.val ≠ 7; assumption
        refine ⟨t, ?_, ?_, ?_, (last_middle_iff rank low high).mpr ⟨sy, ty, Or.inr ⟨sx, by omega⟩⟩⟩
        · simp only [RookSees, RookLine, OnSeg]; omega
        · rw [ne_iff_coords]; omega
        · rw [ne_iff_coords]; omega
      · let t : Square := (⟨wk.1.val + 1, by omega⟩, rs.2)
        have tf : t.1.val = wk.1.val + 1 := rfl
        have ty : t.2.val = rs.2.val := rfl
        have tall : 2 ≤ t.2.val := by omega
        refine ⟨t, ?_, ?_, ?_, (last_middle_iff rank low high).mpr ⟨sy, tall, Or.inr ⟨sx, tf⟩⟩⟩
        · simp only [RookSees, RookLine, OnSeg]; omega
        · rw [ne_iff_coords]; omega
        · rw [ne_iff_coords]; omega

/-- Complete elimination of the coordinate witnesses in the central-edge
three-ply criterion. No move search or recursive outcome predicate remains. -/
theorem three_middle_iff {sk rs wk : Square} (distinct : sk ≠ rs)
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) :
    Three sk rs wk ↔ MiddleThree sk rs wk := by
  simp only [Three, MiddleThree, immediate_middle_iff rank low high,
    king_entry_middle_iff rank low high, rook_entry_middle_iff distinct rank low high,
    or_assoc]

end EndgameChess.Rules.KRKThreePly
