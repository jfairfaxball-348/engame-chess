import EndgameChess.Rules.KRKFourPlySecond
import EndgameChess.Rules.KRKFourPlyInterior

namespace EndgameChess.Rules.KRKFourPlyNearCorner
open EndgameChess.KK KRKThreePly KRKLastReply KRKFourPlyEscape KRKMateGeometry KRKFourPlyMiddle
set_option maxHeartbeats 500000

def NearFour (sk rs : Square) : Prop := sk.2.val = 2 ∧
  ((sk.1.val = 0 ∧ rs.1.val = 2 ∧ 2 ≤ rs.2.val) ∨
   (sk.1.val = 1 ∧ (3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨
     (rs.2.val = 1 ∧ (rs.1.val = 2 ∨ rs.1.val = 3)))) ∨
   (sk.1.val = 2 ∧ ((rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
     (3 ≤ rs.1.val ∧ ¬(rs.1.val = 3 ∧ rs.2.val = 1)))))

private theorem covered_or_corner {sk rs wk t : Square} (distinct : sk ≠ rs)
    (safe : SafeRook sk rs wk) (distance : dInf wk t = 1)
    (file : t.1.val = 0) (rank : t.2.val = 0)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    (sk.1.val ≤ t.1.val + 1 ∧ t.1.val ≤ sk.1.val + 1 ∧
      sk.2.val ≤ t.2.val + 1 ∧ t.2.val ≤ sk.2.val + 1) ∨
      rs.1.val = t.1.val ∨ rs.2.val = t.2.val ∨ CornerThree sk rs := by
  by_cases king : dInf sk t ≤ 1
  · left; simp only [dInf, absDiff] at king; omega
  by_cases line : RookLine rs t
  · exact Or.inr (by rcases line.2 with x | y; exact Or.inl x; exact Or.inr (Or.inl y))
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal, dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have step : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ :=
    StepM.lone distance notRook (by omega) (fun sees => line sees.1)
  exact Or.inr (Or.inr (Or.inr ((three_corner_iff distinct file rank).mp (every t step))))

theorem covered_or_swapped_near {sk rs wk t : Square} (distinct : sk ≠ rs)
    (safe : SafeRook sk rs wk) (distance : dInf wk t = 1)
    (file : t.1.val = 0) (rank : t.2.val = 1)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    (sk.1.val ≤ t.1.val + 1 ∧ t.1.val ≤ sk.1.val + 1 ∧
      sk.2.val ≤ t.2.val + 1 ∧ t.2.val ≤ sk.2.val + 1) ∨
      rs.1.val = t.1.val ∨ rs.2.val = t.2.val ∨ NearThree (sk.2, sk.1) (rs.2, rs.1) := by
  by_cases king : dInf sk t ≤ 1
  · left; simp only [dInf, absDiff] at king; omega
  by_cases line : RookLine rs t
  · exact Or.inr (by rcases line.2 with x | y; exact Or.inl x; exact Or.inr (Or.inl y))
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal, dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have far : 2 ≤ dInf sk t := by omega
  have notCheck : ¬RookSees rs t sk t := fun sees => line sees.1
  have step : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := StepM.lone distance notRook far notCheck
  have mapped := three_map symSwap distinct (ne_of_dInf_pos (by omega)) notRook.symm far notCheck (every t step)
  exact Or.inr (Or.inr (Or.inr ((three_near_iff (symSwap.ne_iff.mpr distinct) rank file).mp mapped)))

private theorem near_eliminate_zero {sk rs wk : Square}
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (a : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (b : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 0 ∨ CornerThree sk rs)
    (r : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 0 ∨ MiddleThree sk rs ((2 : Fin 8), (0 : Fin 8)))
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1)) (sx : sk.1.val = 0) :
    Terminal sk rs wk ∨ NearFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CornerThree, MiddleThree, CoordinateStep, absDiff, sx, sy] at l r c
    simp [Terminal, Horizontal, NearFour, file, rank, absDiff, sx, sy] <;> omega

private theorem near_eliminate_one {sk rs wk : Square}
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (a : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (b : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 0 ∨ CornerThree sk rs)
    (r : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 0 ∨ MiddleThree sk rs ((2 : Fin 8), (0 : Fin 8)))
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1)) (sx : sk.1.val = 1) :
    Terminal sk rs wk ∨ NearFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CornerThree, MiddleThree, CoordinateStep, absDiff, sx, sy] at l r c
    simp [Terminal, Horizontal, NearFour, file, rank, absDiff, sx, sy] <;> omega

private theorem near_eliminate_two {sk rs wk : Square}
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (a : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (b : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 0 ∨ CornerThree sk rs)
    (r : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 0 ∨ MiddleThree sk rs ((2 : Fin 8), (0 : Fin 8)))
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1)) (sx : sk.1.val = 2) :
    Terminal sk rs wk ∨ NearFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CornerThree, MiddleThree, CoordinateStep, absDiff, sx, sy] at l r c
    simp [Terminal, Horizontal, NearFour, file, rank, absDiff, sx, sy] <;> omega

private theorem near_eliminate_three {sk rs wk : Square}
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (a : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (b : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 0 ∨ CornerThree sk rs)
    (r : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 0 ∨ MiddleThree sk rs ((2 : Fin 8), (0 : Fin 8)))
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1)) (sx : sk.1.val = 3) :
    Terminal sk rs wk ∨ NearFour sk rs := by
  simp only [SafeRook, dInf, absDiff, file, rank] at far safe
  simp only [ne_iff_coords] at distinct
  have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  rcases ranks with sy | sy | sy | sy | sy <;> first
  | omega
  | simp [NearThree, CornerThree, MiddleThree, CoordinateStep, absDiff, sx, sy] at l r c
    simp [Terminal, Horizontal, NearFour, file, rank, absDiff, sx, sy] <;> omega

private theorem near_eliminate_outer {sk rs wk : Square}
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (a : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (b : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 0 ∨ CornerThree sk rs)
    (r : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 0 ∨ MiddleThree sk rs ((2 : Fin 8), (0 : Fin 8)))
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1)) (sx : 3 ≤ sk.1.val) :
    Terminal sk rs wk ∨ NearFour sk rs := by
  by_cases third : sk.1.val = 3
  · exact near_eliminate_three file rank far safe distinct a b l r c third
  have large : 4 ≤ sk.1.val := by omega
  have ry : rs.2.val = 1 := by omega
  have noCorner : ¬CornerThree sk rs := by
    simp only [CornerThree, CoordinateStep, absDiff]
    omega
  simp only [noCorner, or_false] at l
  have rx : rs.1.val = 0 := by omega
  simp [MiddleThree, CoordinateStep, absDiff, ry] at r
  exfalso; omega

private theorem near_coordinate_elimination {sk rs wk : Square}
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (distinct : sk ≠ rs)
    (a : (sk.1.val ≤ 2 ∧ 1 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 1 ∨ rs.2.val = 1)
    (b : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 1)
    (l : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 0 ∨ CornerThree sk rs)
    (r : (sk.1.val ≤ 3 ∧ 2 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 1 ∧ 0 ≤ sk.2.val + 1) ∨ rs.1.val = 2 ∨ rs.2.val = 0 ∨ MiddleThree sk rs ((2 : Fin 8), (0 : Fin 8)))
    (c : (sk.1.val ≤ 1 ∧ 0 ≤ sk.1.val + 1 ∧ sk.2.val ≤ 2 ∧ 1 ≤ sk.2.val + 1) ∨ rs.1.val = 0 ∨ rs.2.val = 1 ∨ NearThree (sk.2, sk.1) (rs.2, rs.1)) :
    Terminal sk rs wk ∨ NearFour sk rs := by
  have files : sk.1.val = 0 ∨ sk.1.val = 1 ∨ sk.1.val = 2 ∨ 3 ≤ sk.1.val := by omega
  rcases files with sx | sx | sx | sx
  · exact near_eliminate_zero file rank far safe distinct a b l r c sx
  · exact near_eliminate_one file rank far safe distinct a b l r c sx
  · exact near_eliminate_two file rank far safe distinct a b l r c sx
  · exact near_eliminate_outer file rank far safe distinct a b l r c sx

theorem near_four_necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    Terminal sk rs wk ∨ NearFour sk rs := by
  have a := covered_box (interior_neighbour_covered (t := ((1 : Fin 8), (1 : Fin 8))) safe
    (by simp [dInf, absDiff, file, rank]) (by decide) every)
  have b := covered_box (interior_neighbour_covered (t := ((2 : Fin 8), (1 : Fin 8))) safe
    (by simp [dInf, absDiff, file, rank]) (by decide) every)
  have l := covered_or_corner (t := ((0 : Fin 8), (0 : Fin 8))) distinct safe
    (by simp [dInf, absDiff, file, rank]) rfl rfl every
  have r := covered_or_middle (t := ((2 : Fin 8), (0 : Fin 8))) distinct safe
    (by simp [dInf, absDiff, file, rank]) rfl (by decide) (by decide) every
  have c := covered_or_swapped_near (t := ((0 : Fin 8), (1 : Fin 8))) distinct safe
    (by simp [dInf, absDiff, file, rank]) rfl rfl every
  apply near_coordinate_elimination file rank far safe distinct
  · simpa using a
  · simpa using b
  · simpa using l
  · simpa using r
  · simpa using c

theorem near_four_replies {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) (region : NearFour sk rs) :
    ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u := by
  intro u step
  cases step with
  | lone distance notRook far notCheck =>
    have arrivalFar := far
    have clearRook := notCheck
    have geometry := distance
    simp only [dInf, absDiff, file, rank] at geometry far
    have region' := region
    simp only [NearFour] at region'
    simp only [RookSees, RookLine, OnSeg] at notCheck
    by_cases bottom : u.2.val = 0
    · by_cases corner : u.1.val = 0
      · apply (three_corner_iff distinct corner bottom).mpr
        rcases region' with ⟨sy, ⟨sx, rook⟩ | ⟨sx, rook⟩ | ⟨sx, rook⟩⟩ <;>
          simp [CornerThree, CoordinateStep, absDiff, sx, sy] <;> omega
      · have second : u.1.val = 2 := by omega
        apply (three_middle_iff distinct bottom (by omega) (by omega)).mpr
        rcases region' with ⟨sy, ⟨sx, rook⟩ | ⟨sx, rook⟩ | ⟨sx, rook⟩⟩ <;>
          simp [MiddleThree, CoordinateStep, absDiff, sx, sy, second, bottom] <;> omega
    · have left : u.1.val = 0 ∧ u.2.val = 1 := by omega
      have swapped : Three (symSwap.f sk) (symSwap.f rs) (symSwap.f u) := by
        apply (three_near_iff (symSwap.ne_iff.mpr distinct) left.2 left.1).mpr
        rcases region' with ⟨sy, ⟨sx, rook⟩ | ⟨sx, rook⟩ | ⟨sx, rook⟩⟩ <;>
          simp [symSwap, NearThree, CoordinateStep, absDiff, sx, sy] <;> omega
      have mapped := three_map symSwap (symSwap.ne_iff.mpr distinct)
        (symSwap.ne_iff.mpr (ne_of_dInf_pos (by omega)))
        (symSwap.ne_iff.mpr notRook.symm) (by simpa only [symSwap.dInf_eq] using arrivalFar)
        (fun sees => clearRook ((symSwap.sees_iff _ _ _ _).mp sees)) swapped
      simpa only [symSwap.invol] using mapped

end EndgameChess.Rules.KRKFourPlyNearCorner
