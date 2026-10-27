import EndgameChess.Rules.KRKThreePlyNearCorner

namespace EndgameChess.Rules.KRKThreePly
open EndgameChess.KK KRKMateGeometry KRKImmediate KRKLastReply
set_option maxHeartbeats 500000

def CornerThree (sk rs : Square) : Prop :=
  (sk.2.val = 2 ∧ sk.1.val ≤ 1 ∧ 2 ≤ rs.1.val ∧ rs.2.val ≠ 0) ∨
  (sk.1.val = 2 ∧ sk.2.val ≤ 1 ∧ 2 ≤ rs.2.val ∧ rs.1.val ≠ 0) ∨
  (3 ≤ rs.1.val ∧ 1 ≤ rs.2.val ∧ CoordinateStep sk 1 2) ∨
  (3 ≤ rs.2.val ∧ 1 ≤ rs.1.val ∧ CoordinateStep sk 2 1) ∨
  (sk.1.val = 1 ∧ sk.2.val = 2 ∧
    (3 ≤ rs.1.val ∨ (1 ≤ rs.2.val ∧ (rs.2.val ≠ 2 ∨ 1 < rs.1.val)))) ∨
  (sk.1.val = 2 ∧ sk.2.val = 1 ∧
    (3 ≤ rs.2.val ∨ (1 ≤ rs.1.val ∧ (rs.1.val ≠ 2 ∨ 1 < rs.2.val))))

theorem last_corner_iff {sk rs wk : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    LastReply sk rs wk ↔
      (sk.1.val = 1 ∧ sk.2.val = 2 ∧ 3 ≤ rs.1.val ∧ 1 ≤ rs.2.val) ∨
      (sk.1.val = 2 ∧ sk.2.val = 1 ∧ 3 ≤ rs.2.val ∧ 1 ≤ rs.1.val) := by
  simp [LastReply, HorizontalLast, SafeRook, dInf, absDiff, file, rank]
  omega

theorem immediate_corner_iff {sk rs wk : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    MateNow sk rs wk ↔
      (sk.2.val = 2 ∧ sk.1.val ≤ 1 ∧ 2 ≤ rs.1.val ∧ rs.2.val ≠ 0) ∨
      (sk.1.val = 2 ∧ sk.2.val ≤ 1 ∧ 2 ≤ rs.2.val ∧ rs.1.val ≠ 0) := by
  simp [MateNow, Horizontal, rankTarget, fileTarget, RookSees, RookLine, OnSeg, absDiff, file, rank]
  omega

theorem king_entry_corner_iff {sk rs wk : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    KingEntry sk rs wk ↔
      (3 ≤ rs.1.val ∧ 1 ≤ rs.2.val ∧ CoordinateStep sk 1 2) ∨
      (3 ≤ rs.2.val ∧ 1 ≤ rs.1.val ∧ CoordinateStep sk 2 1) := by
  constructor
  · rintro ⟨t, distance, _, _, last⟩
    rcases (last_corner_iff file rank).mp last with ⟨tx, ty, rx, ry⟩ | ⟨tx, ty, ry, rx⟩
    · exact Or.inl ⟨rx, ry, by simpa only [CoordinateStep, dInf, tx, ty] using distance⟩
    · exact Or.inr ⟨ry, rx, by simpa only [CoordinateStep, dInf, tx, ty] using distance⟩
  · rintro (⟨rx, ry, distance⟩ | ⟨ry, rx, distance⟩)
    · refine ⟨((1 : Fin 8), (2 : Fin 8)), distance, ?_, ?_, (last_corner_iff file rank).mpr ?_⟩
      · rw [ne_iff_coords]; dsimp only; omega
      · simp [dInf, absDiff, file, rank]
      · exact Or.inl ⟨rfl, rfl, rx, ry⟩
    · refine ⟨((2 : Fin 8), (1 : Fin 8)), distance, ?_, ?_, (last_corner_iff file rank).mpr ?_⟩
      · rw [ne_iff_coords]; dsimp only; omega
      · simp [dInf, absDiff, file, rank]
      · exact Or.inr ⟨rfl, rfl, ry, rx⟩

theorem rook_entry_corner_iff {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    RookEntry sk rs wk ↔
      (sk.1.val = 1 ∧ sk.2.val = 2 ∧
        (3 ≤ rs.1.val ∨ (1 ≤ rs.2.val ∧ (rs.2.val ≠ 2 ∨ 1 < rs.1.val)))) ∨
      (sk.1.val = 2 ∧ sk.2.val = 1 ∧
        (3 ≤ rs.2.val ∨ (1 ≤ rs.1.val ∧ (rs.1.val ≠ 2 ∨ 1 < rs.2.val)))) := by
  constructor
  · rintro ⟨t, sees, _, _, last⟩
    simp only [ne_iff_coords] at distinct
    rcases (last_corner_iff file rank).mp last with ⟨sx, sy, tx, ty⟩ | ⟨sx, sy, ty, tx⟩
    · refine Or.inl ⟨sx, sy, ?_⟩
      simp only [RookSees, RookLine, OnSeg] at sees
      omega
    · refine Or.inr ⟨sx, sy, ?_⟩
      simp only [RookSees, RookLine, OnSeg] at sees
      omega
  · rintro (⟨sx, sy, ray⟩ | ⟨sx, sy, ray⟩)
    · by_cases sourceFile : 3 ≤ rs.1.val
      · let y : Fin 8 := if rs.2.val = 7 then 6 else 7
        have height : 1 ≤ y.val := by dsimp [y]; split <;> decide
        have changed : rs.2.val ≠ y.val := by
          dsimp [y]; split
          · change rs.2.val ≠ 6; omega
          · change rs.2.val ≠ 7; assumption
        clear_value y
        refine ⟨(rs.1, y), ?_, ?_, ?_, (last_corner_iff file rank).mpr (Or.inl ⟨sx, sy, sourceFile, height⟩)⟩
        · simp [RookSees, RookLine, OnSeg, sx, sy, file, rank, changed] <;> omega
        · rw [ne_iff_coords]; dsimp only; omega
        · rw [ne_iff_coords]; dsimp only; omega
      · have crossing := ray.resolve_left sourceFile
        refine ⟨((3 : Fin 8), rs.2), ?_, ?_, ?_,
          (last_corner_iff file rank).mpr (Or.inl ⟨sx, sy, by change 3 ≤ 3; decide, crossing.1⟩)⟩
        · simp [RookSees, RookLine, OnSeg, sx, sy, file, rank] <;> omega
        · rw [ne_iff_coords]; dsimp only; omega
        · rw [ne_iff_coords]; dsimp only; omega
    · by_cases sourceRank : 3 ≤ rs.2.val
      · let x : Fin 8 := if rs.1.val = 7 then 6 else 7
        have width : 1 ≤ x.val := by dsimp [x]; split <;> decide
        have changed : rs.1.val ≠ x.val := by
          dsimp [x]; split
          · change rs.1.val ≠ 6; omega
          · change rs.1.val ≠ 7; assumption
        clear_value x
        refine ⟨(x, rs.2), ?_, ?_, ?_, (last_corner_iff file rank).mpr (Or.inr ⟨sx, sy, sourceRank, width⟩)⟩
        · simp [RookSees, RookLine, OnSeg, sx, sy, file, rank, changed] <;> omega
        · rw [ne_iff_coords]; dsimp only; omega
        · rw [ne_iff_coords]; dsimp only; omega
      · have crossing := ray.resolve_left sourceRank
        refine ⟨(rs.1, (3 : Fin 8)), ?_, ?_, ?_,
          (last_corner_iff file rank).mpr (Or.inr ⟨sx, sy, by change 3 ≤ 3; decide, crossing.1⟩)⟩
        · simp [RookSees, RookLine, OnSeg, sx, sy, file, rank] <;> omega
        · rw [ne_iff_coords]; dsimp only; omega
        · rw [ne_iff_coords]; dsimp only; omega

/-- The complete corner three-ply region has six explicit coordinate rows. -/
theorem three_corner_iff {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) : Three sk rs wk ↔ CornerThree sk rs := by
  simp only [Three, CornerThree, immediate_corner_iff file rank, king_entry_corner_iff file rank,
    rook_entry_corner_iff distinct file rank, or_assoc]

end EndgameChess.Rules.KRKThreePly
