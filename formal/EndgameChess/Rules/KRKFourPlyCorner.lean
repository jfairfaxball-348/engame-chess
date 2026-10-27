import EndgameChess.Rules.KRKFourPlyNearKernel

namespace EndgameChess.Rules.KRKFourPlyCorner
open EndgameChess.KK KRKThreePly KRKLastReply KRKFourPlyEscape KRKMateGeometry KRKFourPlyNearCorner
set_option maxHeartbeats 500000

def CornerFour (sk rs : Square) : Prop :=
  (sk.1.val = 0 ∧ sk.2.val = 2 ∧ (2 ≤ rs.2.val ∨ rs.1.val = 2)) ∨
  (sk.1.val = 2 ∧ sk.2.val = 0 ∧ (2 ≤ rs.1.val ∨ rs.2.val = 2)) ∨
  (sk.1.val = 1 ∧ sk.2.val = 2 ∧ 1 ≤ rs.2.val) ∨
  (sk.1.val = 2 ∧ sk.2.val = 1 ∧ 1 ≤ rs.1.val) ∨
  (sk.1.val = 2 ∧ sk.2.val = 2 ∧
    ((3 ≤ rs.1.val ∧ 3 ≤ rs.2.val) ∨ (rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
      (rs.2.val = 0 ∧ 2 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ rs.2.val = 2) ∨
      (rs.1.val = 2 ∧ rs.2.val = 1))) ∨
  (sk.1.val ≤ 2 ∧ sk.2.val = 3 ∧ rs.1.val = 2 ∧ rs.2.val = 1) ∨
  (sk.1.val = 3 ∧ sk.2.val ≤ 2 ∧ rs.1.val = 1 ∧ rs.2.val = 2)

private theorem eliminate_file_0 {sk rs wk : Square}
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (live : ¬(rs.1.val = 1 ∧ rs.2.val = 1 ∧
      ((sk.1.val = 0 ∧ sk.2.val = 2) ∨ (sk.1.val = 2 ∧ sk.2.val = 0) ∨
       (sk.1.val = 2 ∧ sk.2.val = 2))))
    (a : (sk.1.val ≤ 2 ∧ sk.2.val ≤ 2) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 0 ∨ NearThree sk rs)
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1))
    (sx : sk.1.val = 0) : Terminal sk rs wk ∨ CornerFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CoordinateStep, absDiff, sx, sy] at l c
    simp [Terminal, Horizontal, CornerFour, file, rank, absDiff, sx, sy] <;>
      simp only [Fin.ext_iff] at l c ⊢ <;> (try dsimp only at l c ⊢) <;> omega

private theorem eliminate_file_1 {sk rs wk : Square}
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (live : ¬(rs.1.val = 1 ∧ rs.2.val = 1 ∧
      ((sk.1.val = 0 ∧ sk.2.val = 2) ∨ (sk.1.val = 2 ∧ sk.2.val = 0) ∨
       (sk.1.val = 2 ∧ sk.2.val = 2))))
    (a : (sk.1.val ≤ 2 ∧ sk.2.val ≤ 2) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 0 ∨ NearThree sk rs)
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1))
    (sx : sk.1.val = 1) : Terminal sk rs wk ∨ CornerFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CoordinateStep, absDiff, sx, sy] at l c
    simp [Terminal, Horizontal, CornerFour, file, rank, absDiff, sx, sy] <;>
      simp only [Fin.ext_iff] at l c ⊢ <;> (try dsimp only at l c ⊢) <;> omega

private theorem eliminate_file_2 {sk rs wk : Square}
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (live : ¬(rs.1.val = 1 ∧ rs.2.val = 1 ∧
      ((sk.1.val = 0 ∧ sk.2.val = 2) ∨ (sk.1.val = 2 ∧ sk.2.val = 0) ∨
       (sk.1.val = 2 ∧ sk.2.val = 2))))
    (a : (sk.1.val ≤ 2 ∧ sk.2.val ≤ 2) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 0 ∨ NearThree sk rs)
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1))
    (sx : sk.1.val = 2) : Terminal sk rs wk ∨ CornerFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CoordinateStep, absDiff, sx, sy] at l c
    simp [Terminal, Horizontal, CornerFour, file, rank, absDiff, sx, sy] <;>
      simp only [Fin.ext_iff] at l c ⊢ <;> (try dsimp only at l c ⊢) <;> omega

private theorem eliminate_file_3 {sk rs wk : Square}
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (live : ¬(rs.1.val = 1 ∧ rs.2.val = 1 ∧
      ((sk.1.val = 0 ∧ sk.2.val = 2) ∨ (sk.1.val = 2 ∧ sk.2.val = 0) ∨
       (sk.1.val = 2 ∧ sk.2.val = 2))))
    (a : (sk.1.val ≤ 2 ∧ sk.2.val ≤ 2) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 0 ∨ NearThree sk rs)
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1))
    (sx : sk.1.val = 3) : Terminal sk rs wk ∨ CornerFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CoordinateStep, absDiff, sx, sy] at l c
    simp [Terminal, Horizontal, CornerFour, file, rank, absDiff, sx, sy] <;>
      simp only [Fin.ext_iff] at l c ⊢ <;> (try dsimp only at l c ⊢) <;> omega

private theorem eliminate_outer {sk rs wk : Square}
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (live : ¬(rs.1.val = 1 ∧ rs.2.val = 1 ∧
      ((sk.1.val = 0 ∧ sk.2.val = 2) ∨ (sk.1.val = 2 ∧ sk.2.val = 0) ∨
       (sk.1.val = 2 ∧ sk.2.val = 2))))
    (a : (sk.1.val ≤ 2 ∧ sk.2.val ≤ 2) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 0 ∨ NearThree sk rs)
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1))
    (sx : 4 ≤ sk.1.val) : Terminal sk rs wk ∨ CornerFour sk rs := by
  have noNear : ¬NearThree sk rs := by simp only [NearThree, CoordinateStep, absDiff]; omega
  have noSwap : ¬NearThree (sk.2, sk.1) (rs.2, rs.1) := by
    simp only [NearThree, CoordinateStep, absDiff]; omega
  simp only [noNear, or_false] at l
  simp only [noSwap, or_false] at c
  have ry : rs.2.val = 1 := by omega
  have rx : rs.1.val = 1 := by omega
  simp only [SafeRook, dInf, absDiff, file, rank] at safe
  exfalso; omega

theorem corner_four_necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (nonempty : ∃ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    Terminal sk rs wk ∨ CornerFour sk rs := by
  have a := covered_box (interior_neighbour_covered (t := ((1 : Fin 8), (1 : Fin 8))) safe
    (by simp [dInf, absDiff, file, rank]) (by decide) every)
  have l := KRKFourPlySecond.covered_or_near (t := ((1 : Fin 8), (0 : Fin 8))) distinct safe
    (by simp [dInf, absDiff, file, rank]) rfl rfl every
  have c := covered_or_swapped_near (t := ((0 : Fin 8), (1 : Fin 8))) distinct safe
    (by simp [dInf, absDiff, file, rank]) rfl rfl every
  have live : ¬(rs.1.val = 1 ∧ rs.2.val = 1 ∧
      ((sk.1.val = 0 ∧ sk.2.val = 2) ∨ (sk.1.val = 2 ∧ sk.2.val = 0) ∨
       (sk.1.val = 2 ∧ sk.2.val = 2))) := by
    rintro ⟨rx, ry, king⟩
    obtain ⟨u, step⟩ := nonempty
    cases step with
    | lone distance _ far notCheck =>
      simp only [dInf, absDiff, file, rank] at distance far
      simp only [RookSees, RookLine, OnSeg] at notCheck
      omega
  have coordA : (sk.1.val ≤ 2 ∧ sk.2.val ≤ 2) ∨ rs.1.val = 1 ∨ rs.2.val = 1 := by simpa using a
  have files : sk.1.val = 0 ∨ sk.1.val = 1 ∨ sk.1.val = 2 ∨ sk.1.val = 3 ∨ 4 ≤ sk.1.val := by omega
  rcases files with sx | sx | sx | sx | sx
  · apply eliminate_file_0 file rank far safe distinct live coordA
    · simpa using l
    · simpa using c
    · exact sx
  · apply eliminate_file_1 file rank far safe distinct live coordA
    · simpa using l
    · simpa using c
    · exact sx
  · apply eliminate_file_2 file rank far safe distinct live coordA
    · simpa using l
    · simpa using c
    · exact sx
  · apply eliminate_file_3 file rank far safe distinct live coordA
    · simpa using l
    · simpa using c
    · exact sx
  · apply eliminate_outer file rank far safe distinct live coordA
    · simpa using l
    · simpa using c
    · exact sx

theorem corner_four_replies {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) (region : CornerFour sk rs) :
    ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u := by
  have separated := distinct
  rw [ne_iff_coords] at separated
  intro u step
  cases step with
  | lone distance notRook far notCheck =>
    have arrivalFar := far
    have clearRook := notCheck
    simp only [dInf, absDiff, file, rank] at distance far
    have region' := region
    simp only [CornerFour] at region'
    simp only [RookSees, RookLine, OnSeg] at notCheck
    have edge : (u.1.val = 1 ∧ u.2.val = 0) ∨ (u.1.val = 0 ∧ u.2.val = 1) := by omega
    rcases edge with ⟨ux, uy⟩ | ⟨ux, uy⟩
    · apply (three_near_iff distinct ux uy).mpr
      rcases region' with ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ |
        ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ <;>
        simp [NearThree, CoordinateStep, absDiff, sx, sy] <;> omega
    · have swapped : Three (symSwap.f sk) (symSwap.f rs) (symSwap.f u) := by
        apply (three_near_iff (symSwap.ne_iff.mpr distinct) uy ux).mpr
        rcases region' with ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ |
          ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ | ⟨sx, sy, rook⟩ <;>
          simp [symSwap, NearThree, CoordinateStep, absDiff, sx, sy] <;> omega
      have mapped := three_map symSwap (symSwap.ne_iff.mpr distinct)
        (symSwap.ne_iff.mpr (ne_of_dInf_pos (by omega)))
        (symSwap.ne_iff.mpr notRook.symm) (by simpa only [symSwap.dInf_eq] using arrivalFar)
        (fun sees => clearRook ((symSwap.sees_iff _ _ _ _).mp sees)) swapped
      simpa only [symSwap.invol] using mapped

end EndgameChess.Rules.KRKFourPlyCorner
