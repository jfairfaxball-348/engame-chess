import EndgameChess.Rules.KRKThreePlyMiddle

namespace EndgameChess.Rules.KRKThreePly
open EndgameChess.KK KRKMateGeometry KRKImmediate KRKLastReply
set_option maxHeartbeats 500000

def NearThree (sk rs : Square) : Prop :=
  (sk.1.val = 1 ∧ sk.2.val = 2 ∧ rs.2.val ≠ 0 ∧ 3 ≤ rs.1.val) ∨
  (2 ≤ rs.2.val ∧ rs.1.val = 0 ∧ CoordinateStep sk 2 2) ∨
  (2 ≤ rs.2.val ∧ rs.1.val = 2 ∧ CoordinateStep sk 0 2) ∨
  (1 ≤ rs.2.val ∧ rs.1.val = 2 ∧ CoordinateStep sk 1 2) ∨
  (sk.1.val = 2 ∧ sk.2.val = 2 ∧
    (rs.1.val = 0 ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ rs.1.val < 2))) ∨
  (sk.1.val = 0 ∧ sk.2.val = 2 ∧
    (rs.1.val = 2 ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 0 < rs.1.val))) ∨
  (sk.1.val = 1 ∧ sk.2.val = 2 ∧
    (rs.1.val = 2 ∨ rs.2.val = 1 ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 1 < rs.1.val)))

theorem last_near_iff {sk rs wk : Square} (file : wk.1.val = 1) (rank : wk.2.val = 0) :
    LastReply sk rs wk ↔ sk.2.val = 2 ∧
      ((sk.1.val = 2 ∧ rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
       (sk.1.val = 0 ∧ rs.1.val = 2 ∧ 2 ≤ rs.2.val) ∨
       (sk.1.val = 1 ∧ rs.1.val = 2 ∧ 1 ≤ rs.2.val)) := by
  simp [LastReply, HorizontalLast, SafeRook, dInf, absDiff, file, rank]
  omega

theorem immediate_near_iff {sk rs wk : Square} (file : wk.1.val = 1) (rank : wk.2.val = 0) :
    MateNow sk rs wk ↔ sk.1.val = 1 ∧ sk.2.val = 2 ∧ rs.2.val ≠ 0 ∧ 3 ≤ rs.1.val := by
  simp [MateNow, Horizontal, rankTarget, fileTarget, RookSees, RookLine, OnSeg, absDiff, file, rank]
  omega

theorem king_entry_near_iff {sk rs wk : Square} (file : wk.1.val = 1) (rank : wk.2.val = 0) :
    KingEntry sk rs wk ↔
      (2 ≤ rs.2.val ∧ rs.1.val = 0 ∧ CoordinateStep sk 2 2) ∨
      (2 ≤ rs.2.val ∧ rs.1.val = 2 ∧ CoordinateStep sk 0 2) ∨
      (1 ≤ rs.2.val ∧ rs.1.val = 2 ∧ CoordinateStep sk 1 2) := by
  constructor
  · rintro ⟨t, distance, _, _, last⟩
    obtain ⟨ty, ⟨tx, rx, ry⟩ | ⟨tx, rx, ry⟩ | ⟨tx, rx, ry⟩⟩ := (last_near_iff file rank).mp last
    · exact Or.inl ⟨ry, rx, by simpa only [CoordinateStep, dInf, tx, ty] using distance⟩
    · exact Or.inr (Or.inl ⟨ry, rx, by simpa only [CoordinateStep, dInf, tx, ty] using distance⟩)
    · exact Or.inr (Or.inr ⟨ry, rx, by simpa only [CoordinateStep, dInf, tx, ty] using distance⟩)
  · rintro (⟨ry, rx, distance⟩ | ⟨ry, rx, distance⟩ | ⟨ry, rx, distance⟩)
    · refine ⟨((2 : Fin 8), (2 : Fin 8)), distance, ?_, ?_, (last_near_iff file rank).mpr ?_⟩
      · rw [ne_iff_coords]; dsimp only; omega
      · simp [dInf, absDiff, file, rank]
      · exact ⟨rfl, Or.inl ⟨rfl, rx, ry⟩⟩
    · refine ⟨((0 : Fin 8), (2 : Fin 8)), distance, ?_, ?_, (last_near_iff file rank).mpr ?_⟩
      · rw [ne_iff_coords]; dsimp only; omega
      · simp [dInf, absDiff, file, rank]
      · exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rx, ry⟩)⟩
    · refine ⟨((1 : Fin 8), (2 : Fin 8)), distance, ?_, ?_, (last_near_iff file rank).mpr ?_⟩
      · rw [ne_iff_coords]; dsimp only; omega
      · simp [dInf, absDiff, file, rank]
      · exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rx, ry⟩)⟩

private theorem rook_entry_on_file {sk rs wk : Square} {f : Fin 8} {b : Nat}
    (notKing : f.val ≠ sk.1.val) (notWeak : f.val ≠ wk.1.val) (bound : b ≤ 6)
    (last : ∀ y : Fin 8, b ≤ y.val → LastReply sk (f, y) wk)
    (ray : rs.1.val = f.val ∨ (b ≤ rs.2.val ∧ RookSees rs (f, rs.2) sk wk)) : RookEntry sk rs wk := by
  by_cases sourceFile : rs.1.val = f.val
  · let y : Fin 8 := if rs.2.val = 7 then 6 else 7
    have height : b ≤ y.val := by
      dsimp [y]; split
      · change b ≤ 6; exact bound
      · change b ≤ 7; omega
    have changed : rs.2.val ≠ y.val := by
      dsimp [y]; split
      · change rs.2.val ≠ 6; omega
      · change rs.2.val ≠ 7; assumption
    refine ⟨(f, y), ?_, ?_, ?_, last y height⟩
    · simp only [RookSees, RookLine, OnSeg]; omega
    · rw [ne_iff_coords]; dsimp only; omega
    · rw [ne_iff_coords]; dsimp only; omega
  · obtain ⟨height, sees⟩ := ray.resolve_left sourceFile
    refine ⟨(f, rs.2), sees, ?_, ?_, last rs.2 height⟩
    · rw [ne_iff_coords]; dsimp only; omega
    · rw [ne_iff_coords]; dsimp only; omega

theorem rook_entry_near_iff {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) :
    RookEntry sk rs wk ↔
      (sk.1.val = 2 ∧ sk.2.val = 2 ∧
        (rs.1.val = 0 ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ rs.1.val < 2))) ∨
      (sk.1.val = 0 ∧ sk.2.val = 2 ∧
        (rs.1.val = 2 ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 0 < rs.1.val))) ∨
      (sk.1.val = 1 ∧ sk.2.val = 2 ∧
        (rs.1.val = 2 ∨ rs.2.val = 1 ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 1 < rs.1.val))) := by
  constructor
  · rintro ⟨t, sees, _, _, last⟩
    simp only [ne_iff_coords] at distinct
    obtain ⟨sy, ⟨sx, tx, ty⟩ | ⟨sx, tx, ty⟩ | ⟨sx, tx, ty⟩⟩ := (last_near_iff file rank).mp last
    · left
      refine ⟨sx, sy, ?_⟩
      simp only [RookSees, RookLine, OnSeg] at sees
      omega
    · right; left
      refine ⟨sx, sy, ?_⟩
      simp only [RookSees, RookLine, OnSeg] at sees
      omega
    · right; right
      refine ⟨sx, sy, ?_⟩
      simp only [RookSees, RookLine, OnSeg] at sees
      omega
  · rintro (⟨sx, sy, ray⟩ | ⟨sx, sy, ray⟩ | ⟨sx, sy, ray⟩)
    · apply rook_entry_on_file (f := (0 : Fin 8)) (b := 2) (by omega) (by omega) (by decide)
      · intro y height
        exact (last_near_iff file rank).mpr ⟨sy, Or.inl ⟨sx, rfl, height⟩⟩
      · by_cases sourceFile : rs.1.val = 0
        · exact Or.inl sourceFile
        · right; refine ⟨by omega, ?_⟩
          simp [RookSees, RookLine, OnSeg, sx, sy, file, rank] <;> omega
    · apply rook_entry_on_file (f := (2 : Fin 8)) (b := 2) (by omega) (by omega) (by decide)
      · intro y height
        exact (last_near_iff file rank).mpr ⟨sy, Or.inr (Or.inl ⟨sx, rfl, height⟩)⟩
      · by_cases sourceFile : rs.1.val = 2
        · exact Or.inl sourceFile
        · right; refine ⟨by omega, ?_⟩
          simp [RookSees, RookLine, OnSeg, sx, sy, file, rank] <;> omega
    · apply rook_entry_on_file (f := (2 : Fin 8)) (b := 1) (by omega) (by omega) (by decide)
      · intro y height
        exact (last_near_iff file rank).mpr ⟨sy, Or.inr (Or.inr ⟨sx, rfl, height⟩)⟩
      · by_cases sourceFile : rs.1.val = 2
        · exact Or.inl sourceFile
        · right; refine ⟨by omega, ?_⟩
          simp [RookSees, RookLine, OnSeg, sx, sy, file, rank] <;> omega

theorem three_near_iff {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) : Three sk rs wk ↔ NearThree sk rs := by
  simp only [Three, NearThree, immediate_near_iff file rank, king_entry_near_iff file rank,
    rook_entry_near_iff distinct file rank, or_assoc]

end EndgameChess.Rules.KRKThreePly
