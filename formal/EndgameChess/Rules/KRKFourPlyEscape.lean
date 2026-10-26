import EndgameChess.Rules.KRKThreePlyHistory

namespace EndgameChess.Rules.KRKFourPlyEscape
open EndgameChess.KK KRKLastReply KRKImmediate KRKThreePly
set_option maxHeartbeats 1000000

theorem last_depth_zero {sk rs wk : Square} (last : LastReply sk rs wk) :
    KRKEdgeDepth.depth wk = 0 := by
  rcases last.2 with horizontal | vertical
  · obtain ⟨edge, _⟩ := horizontal
    simp only [KRKEdgeDepth.depth] at *
    omega
  · obtain ⟨edge, _⟩ := vertical
    simp only [KRKEdgeDepth.depth] at *
    omega

/-- Every strong three-ply mate starts with the weak king on an edge. -/
theorem three_depth_zero {sk rs wk : Square} (three : Three sk rs wk) :
    KRKEdgeDepth.depth wk = 0 := by
  rcases three with immediate | king | rook
  · rcases immediate with ⟨horizontal, _⟩ | ⟨vertical, _⟩
    · obtain ⟨_, edge, _⟩ := horizontal
      simp only [KRKEdgeDepth.depth]; omega
    · obtain ⟨_, edge, _⟩ := vertical
      dsimp only at edge
      simp only [KRKEdgeDepth.depth]; omega
  · obtain ⟨_, _, _, _, last⟩ := king
    exact last_depth_zero last
  · obtain ⟨_, _, _, _, last⟩ := rook
    exact last_depth_zero last

def Covered (sk rs t : Square) : Prop := dInf sk t ≤ 1 ∨ RookLine rs t

/-- A safe-rook weak root with every reply in the three-ply region must
cover every neighbouring interior square by its king or a rook line. -/
theorem interior_neighbour_covered {sk rs wk t : Square}
    (safe : SafeRook sk rs wk) (step : dInf wk t = 1)
    (inside : 0 < KRKEdgeDepth.depth t)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal, dInf_comm] at step; omega
    · rw [equal] at king; omega
  have legal : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ :=
    StepM.lone step notRook (by omega) (fun sees => line sees.1)
  have zero := three_depth_zero (every t legal)
  omega

theorem covered_box {sk rs t : Square} (covered : Covered sk rs t) :
    (sk.1.val ≤ t.1.val + 1 ∧ t.1.val ≤ sk.1.val + 1 ∧
      sk.2.val ≤ t.2.val + 1 ∧ t.2.val ≤ sk.2.val + 1) ∨
      rs.1.val = t.1.val ∨ rs.2.val = t.2.val := by
  simp only [Covered, RookLine, dInf, absDiff] at covered
  omega

/-- Covering the five inward neighbours of a noncorner first-band king
forces the king directly opposite and the rook on its file. -/
theorem strip_prison {sk rs wk : Square}
    (file : wk.1.val = 1) (low : 2 ≤ wk.2.val) (high : wk.2.val ≤ 5)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t) :
    sk.1.val = 3 ∧ sk.2.val = wk.2.val ∧ rs.1.val = 1 := by
  let down : Fin 8 := ⟨wk.2.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.2.isLt⟩
  let up : Fin 8 := ⟨wk.2.val + 1, by omega⟩
  have a := covered_box (cover ((1 : Fin 8), down) (by simp [dInf, absDiff, down, file] <;> omega)
    (by simp [KRKEdgeDepth.depth, down] <;> omega))
  have b := covered_box (cover ((1 : Fin 8), up) (by simp [dInf, absDiff, up, file] <;> omega)
    (by simp [KRKEdgeDepth.depth, up] <;> omega))
  have c := covered_box (cover ((2 : Fin 8), down) (by simp [dInf, absDiff, down, file] <;> omega)
    (by simp [KRKEdgeDepth.depth, down] <;> omega))
  have d := covered_box (cover ((2 : Fin 8), wk.2) (by simp [dInf, absDiff, file] <;> omega)
    (by simp [KRKEdgeDepth.depth] <;> omega))
  have e := covered_box (cover ((2 : Fin 8), up) (by simp [dInf, absDiff, up, file] <;> omega)
    (by simp [KRKEdgeDepth.depth, up] <;> omega))
  clear cover
  simp [down, up] at a b c d e
  have kingFar : 3 ≤ sk.1.val ∨ sk.2.val + 2 ≤ wk.2.val ∨ wk.2.val + 2 ≤ sk.2.val := by
    simp only [dInf, absDiff, file] at far
    omega
  clear far
  simp only [SafeRook, dInf, absDiff, file] at safe
  by_cases rookFile : rs.1.val = 1
  · omega
  · omega

def CornerPrison (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ sk.2.val ≤ 2 ∧ rs.2.val = 2) ∨
  (sk.2.val = 3 ∧ sk.1.val ≤ 2 ∧ rs.1.val = 2) ∨
  (sk.1.val = 3 ∧ (sk.2.val = 1 ∨ sk.2.val = 2) ∧ rs.1.val = 1) ∨
  (sk.2.val = 3 ∧ (sk.1.val = 1 ∨ sk.1.val = 2) ∧ rs.2.val = 1) ∨
  (sk.1.val = 3 ∧ sk.2.val = 3 ∧ rs.1.val = 2 ∧ rs.2.val = 2)

/-- The three inward neighbours of b2 can all be covered only in these five
geometric families. These are necessary regions, not enumerated positions. -/
theorem corner_prison {sk rs wk : Square} (file : wk.1.val = 1) (rank : wk.2.val = 1)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t) :
    CornerPrison sk rs := by
  have a := covered_box (cover ((1 : Fin 8), (2 : Fin 8))
    (by simp [dInf, absDiff, file, rank]) (by decide))
  have b := covered_box (cover ((2 : Fin 8), (1 : Fin 8))
    (by simp [dInf, absDiff, file, rank]) (by decide))
  have c := covered_box (cover ((2 : Fin 8), (2 : Fin 8))
    (by simp [dInf, absDiff, file, rank]) (by decide))
  clear cover
  simp at a b c
  simp only [dInf, absDiff, file, rank, SafeRook] at far safe
  by_cases sx : sk.1.val = 3
  · by_cases sy : sk.2.val = 3
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨sx, sy, by omega, by omega⟩)))
    · have bound : sk.2.val ≤ 2 := by omega
      by_cases ry : rs.2.val = 2
      · exact Or.inl ⟨sx, bound, ry⟩
      · exact Or.inr (Or.inr (Or.inl ⟨sx, by omega, by omega⟩))
  · by_cases sy : sk.2.val = 3
    · have bound : sk.1.val ≤ 2 := by omega
      by_cases rx : rs.1.val = 2
      · exact Or.inr (Or.inl ⟨sy, bound, rx⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨sy, by omega, by omega⟩)))
    · exact False.elim (by omega)

private theorem no_three_south {sk rs : Square}
    (sx : sk.1.val = 3) (sy : sk.2.val ≤ 2)
    (rx : 2 ≤ rs.1.val) (ry : rs.2.val = 2) :
    ¬Three sk rs ((1 : Fin 8), (0 : Fin 8)) := by
  rintro (immediate | king | rook)
  · simp [MateNow, KRKMateGeometry.Horizontal, rankTarget, fileTarget] at immediate
    omega
  · obtain ⟨t, distance, _, _, _, last⟩ := king
    simp [HorizontalLast, dInf, absDiff, sx] at distance last
    omega
  · obtain ⟨t, _, _, _, _, last⟩ := rook
    simp [HorizontalLast, sx] at last <;> omega

private theorem no_three_west {sk rs : Square}
    (sy : sk.2.val = 3) (sx : sk.1.val ≤ 2)
    (ry : 2 ≤ rs.2.val) (rx : rs.1.val = 2) :
    ¬Three sk rs ((0 : Fin 8), (1 : Fin 8)) := by
  rintro (immediate | king | rook)
  · simp [MateNow, KRKMateGeometry.Horizontal, rankTarget, fileTarget] at immediate
    omega
  · obtain ⟨t, distance, _, _, _, last⟩ := king
    simp [HorizontalLast, dInf, absDiff, sy] at distance last
    omega
  · obtain ⟨t, _, _, _, _, last⟩ := rook
    simp [HorizontalLast, sy] at last <;> omega

private theorem no_three_west_file {sk rs : Square}
    (sx : sk.1.val = 3) (ry : 3 ≤ rs.2.val) :
    ¬Three sk rs ((0 : Fin 8), (1 : Fin 8)) := by
  rintro (immediate | king | rook)
  · simp [MateNow, KRKMateGeometry.Horizontal, rankTarget, fileTarget] at immediate
    omega
  · obtain ⟨t, distance, _, _, _, last⟩ := king
    simp [HorizontalLast, dInf, absDiff, sx] at distance last
    omega
  · obtain ⟨t, _, _, _, _, last⟩ := rook
    simp [HorizontalLast, sx] at last <;> omega

private theorem no_three_south_rank {sk rs : Square}
    (sy : sk.2.val = 3) (rx : 3 ≤ rs.1.val) :
    ¬Three sk rs ((1 : Fin 8), (0 : Fin 8)) := by
  rintro (immediate | king | rook)
  · simp [MateNow, KRKMateGeometry.Horizontal, rankTarget, fileTarget] at immediate
    omega
  · obtain ⟨t, distance, _, _, _, last⟩ := king
    simp [HorizontalLast, dInf, absDiff, sy] at distance last
    omega
  · obtain ⟨t, _, _, _, _, last⟩ := rook
    simp [HorizontalLast, sy] at last <;> omega

private theorem no_three_corner {sk rs : Square} (sx : sk.1.val = 3) (sy : sk.2.val = 3) :
    ¬Three sk rs ((0 : Fin 8), (0 : Fin 8)) := by
  rintro (immediate | king | rook)
  · simp [MateNow, KRKMateGeometry.Horizontal, rankTarget, fileTarget] at immediate
    omega
  · obtain ⟨t, distance, _, _, _, last⟩ := king
    simp [HorizontalLast, dInf, absDiff, sx, sy] at distance last
    omega
  · obtain ⟨t, _, _, _, _, last⟩ := rook
    simp [HorizontalLast, sx, sy] at last <;> omega

macro "escape_geo" : tactic =>
  `(tactic| (simp_all [dInf, absDiff, ne_iff_coords, RookSees, RookLine, OnSeg] <;> omega))

/-- A b2 weak king has an actual geometric reply outside every three-ply
strong winning region, even when all inward neighbours are covered. -/
theorem corner_escape {sk rs wk : Square} (file : wk.1.val = 1) (rank : wk.2.val = 1)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) : False := by
  have cover := fun (t : Square) (ht : dInf wk t = 1) (hi : 0 < KRKEdgeDepth.depth t) => interior_neighbour_covered safe ht hi every
  rcases corner_prison file rank far safe cover with
    ⟨sx, sy, ry⟩ | ⟨sy, sx, rx⟩ | ⟨sx, sy, rx⟩ | ⟨sy, sx, ry⟩ | ⟨sx, sy, rx, ry⟩
  · have rookFile : 2 ≤ rs.1.val := by
      simp only [SafeRook, dInf, absDiff, file, rank, sx, ry] at safe
      omega
    apply no_three_south sx sy rookFile ry
    apply every ((1 : Fin 8), (0 : Fin 8))
    refine StepM.lone ?_ ?_ ?_ ?_ <;> escape_geo
  · have rookRank : 2 ≤ rs.2.val := by
      simp only [SafeRook, dInf, absDiff, file, rank, sy, rx] at safe
      omega
    apply no_three_west sy sx rookRank rx
    apply every ((0 : Fin 8), (1 : Fin 8))
    refine StepM.lone ?_ ?_ ?_ ?_ <;> escape_geo
  · have rookRank : 3 ≤ rs.2.val := by
      simp only [SafeRook, dInf, absDiff, file, rank, sx, rx] at safe
      omega
    apply no_three_west_file sx rookRank
    apply every ((0 : Fin 8), (1 : Fin 8))
    refine StepM.lone ?_ ?_ ?_ ?_ <;> escape_geo
  · have rookFile : 3 ≤ rs.1.val := by
      simp only [SafeRook, dInf, absDiff, file, rank, sy, ry] at safe
      omega
    apply no_three_south_rank sy rookFile
    apply every ((1 : Fin 8), (0 : Fin 8))
    refine StepM.lone ?_ ?_ ?_ ?_ <;> escape_geo
  · apply no_three_corner sx sy
    apply every ((0 : Fin 8), (0 : Fin 8))
    refine StepM.lone ?_ ?_ ?_ ?_ <;> escape_geo

private theorem no_three_strip {sk rs wk : Square} (file : wk.1.val = 1)
    (low : 2 ≤ wk.2.val) (high : wk.2.val ≤ 5) (sx : sk.1.val = 3)
    (rookRank : rs.2.val + 2 ≤ wk.2.val ∨ wk.2.val + 2 ≤ rs.2.val) :
    ¬Three sk rs ((0 : Fin 8), wk.2) := by
  rintro (immediate | king | rook)
  · simp [MateNow, KRKMateGeometry.Horizontal, rankTarget, fileTarget] at immediate
    omega
  · obtain ⟨t, distance, _, _, _, last⟩ := king
    simp [HorizontalLast, dInf, absDiff, sx] at distance last
    omega
  · obtain ⟨t, _, _, _, _, last⟩ := rook
    simp [HorizontalLast, sx] at last <;> omega

theorem strip_escape {sk rs wk : Square}
    (file : wk.1.val = 1) (low : 2 ≤ wk.2.val) (high : wk.2.val ≤ 5)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) : False := by
  have cover := fun (t : Square) (ht : dInf wk t = 1) (hi : 0 < KRKEdgeDepth.depth t) => interior_neighbour_covered safe ht hi every
  obtain ⟨sx, sy, rx⟩ := strip_prison file low high far safe cover
  have rookRank : rs.2.val + 2 ≤ wk.2.val ∨ wk.2.val + 2 ≤ rs.2.val := by
    simp only [SafeRook, dInf, absDiff, file, sx, sy, rx] at safe
    omega
  apply no_three_strip file low high sx rookRank
  apply every ((0 : Fin 8), wk.2)
  refine StepM.lone ?_ ?_ ?_ ?_ <;> escape_geo

end EndgameChess.Rules.KRKFourPlyEscape
