import EndgameChess.Rules.KRKThreePlyMiddle
import EndgameChess.Rules.KRKFourPlyEscape

namespace EndgameChess.Rules.KRKFourPlyMiddle
open EndgameChess.KK KRKThreePly KRKLastReply KRKFourPlyEscape KRKMateGeometry
set_option maxHeartbeats 4000000

private theorem covered_or_middle {sk rs wk t : Square} (distinct : sk ≠ rs)
    (safe : SafeRook sk rs wk) (distance : dInf wk t = 1)
    (rank : t.2.val = 0) (low : 2 ≤ t.1.val) (high : t.1.val ≤ 5)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    (sk.1.val ≤ t.1.val + 1 ∧ t.1.val ≤ sk.1.val + 1 ∧
      sk.2.val ≤ t.2.val + 1 ∧ t.2.val ≤ sk.2.val + 1) ∨
      rs.1.val = t.1.val ∨ rs.2.val = t.2.val ∨ MiddleThree sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · left
    simp only [dInf, absDiff] at king
    omega
  by_cases line : RookLine rs t
  · exact Or.inr (by rcases line.2 with x | y; exact Or.inl x; exact Or.inr (Or.inl y))
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal, dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have step : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := StepM.lone distance notRook (by omega) (fun sees => line sees.1)
  exact Or.inr (Or.inr (Or.inr ((three_middle_iff distinct rank low high).mp (every t step))))

/-- Necessity for the two central edge files: the full four-ply region is
terminal mate, the earlier last-reply region, or distant-rook opposition. -/
theorem central_four_necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    Terminal sk rs wk ∨ LastReply sk rs wk ∨
      (sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ 3 ≤ rs.2.val) := by
  let left : Fin 8 := ⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩
  let right : Fin 8 := ⟨wk.1.val + 1, by omega⟩
  have a := covered_box (interior_neighbour_covered (t := (left, (1 : Fin 8))) safe
    (by simp [dInf, absDiff, left, rank] <;> omega)
    (by simp [KRKEdgeDepth.depth, left] <;> omega) every)
  have b := covered_box (interior_neighbour_covered (t := (wk.1, (1 : Fin 8))) safe
    (by simp [dInf, absDiff, rank] <;> omega)
    (by simp [KRKEdgeDepth.depth] <;> omega) every)
  have c := covered_box (interior_neighbour_covered (t := (right, (1 : Fin 8))) safe
    (by simp [dInf, absDiff, right, rank] <;> omega)
    (by simp [KRKEdgeDepth.depth, right] <;> omega) every)
  have l := covered_or_middle (t := (left, (0 : Fin 8))) distinct safe
    (by simp [dInf, absDiff, left, rank] <;> omega) rfl (by dsimp [left]; omega) (by dsimp [left]; omega) every
  have r := covered_or_middle (t := (right, (0 : Fin 8))) distinct safe
    (by simp [dInf, absDiff, right, rank] <;> omega) rfl (by dsimp [right]; omega) (by dsimp [right]; omega) every
  clear every
  simp [left, right] at a b c
  simp only [dInf, absDiff, rank] at far
  have prison : sk.2.val = 2 ∨ rs.2.val = 1 := by omega
  by_cases sy : sk.2.val = 2
  · by_cases ry0 : rs.2.val = 0
    · left
      simp [Terminal, Horizontal, rank, sy, ry0, absDiff]
      simp only [SafeRook, dInf, absDiff, rank, sy, ry0] at safe
      omega
    by_cases ry1 : rs.2.val = 1
    · exfalso
      simp [MiddleThree, CoordinateStep, sy, ry1, left, right, absDiff] at l r
      simp only [SafeRook, dInf, absDiff, rank, sy, ry1] at safe
      omega
    by_cases ry2 : rs.2.val = 2
    · right; left
      apply (last_middle_iff rank (by omega) (by omega)).mpr
      simp [MiddleThree, CoordinateStep, sy, ry2, left, right, absDiff] at l r
      simp only [ne_iff_coords] at distinct
      omega
    · have tall : 3 ≤ rs.2.val := by omega
      by_cases same : sk.1.val = wk.1.val
      · exact Or.inr (Or.inr ⟨same, sy, tall⟩)
      · right; left
        apply (last_middle_iff rank (by omega) (by omega)).mpr
        omega
  · have ry : rs.2.val = 1 := prison.resolve_left sy
    exfalso
    simp [MiddleThree, CoordinateStep, sy, ry, left, right, absDiff] at l r
    simp only [SafeRook, dInf, absDiff, rank, ry] at safe
    omega

/-- Direct opposition with a rook three ranks inward keeps every legal
weak reply inside the complete three-ply region. -/
theorem opposition_replies {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u := by
  intro u step
  cases step with
  | lone distance _ far _ =>
    have geometry := distance
    simp only [dInf, absDiff, rank, sx, sy] at geometry far
    have uy : u.2.val = 0 := by omega
    have ux : u.1.val + 1 = wk.1.val ∨ u.1.val = wk.1.val + 1 := by omega
    have distinct : sk ≠ rs := by rw [ne_iff_coords]; omega
    apply (three_middle_iff distinct uy (by omega) (by omega)).mpr
    rcases ux with left | right
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, sy, Or.inr (Or.inl ry)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, sy, Or.inr (Or.inl ry)⟩)))

private theorem opposition_nonempty {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    ∃ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ := by
  by_cases rookLeft : rs.1.val + 1 = wk.1.val
  · let u : Square := (⟨wk.1.val + 1, by omega⟩, (0 : Fin 8))
    refine ⟨u, StepM.lone ?_ ?_ ?_ ?_⟩
    · simp [dInf, absDiff, u, rank] <;> omega
    · rw [ne_iff_coords]; dsimp [u]; omega
    · simp [dInf, absDiff, u, sx, sy] <;> omega
    · simp [RookSees, RookLine, u]; omega
  · let u : Square := (⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩, (0 : Fin 8))
    refine ⟨u, StepM.lone ?_ ?_ ?_ ?_⟩
    · simp [dInf, absDiff, u, rank] <;> omega
    · rw [ne_iff_coords]; dsimp [u]; omega
    · simp [dInf, absDiff, u, sx, sy] <;> omega
    · simp [RookSees, RookLine, u]; omega

theorem weak_four_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (rank : wk.2.val = 0)
    (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4) :
    MateWithin σ 4 q ↔ MatedK q ∨ LastReply sk rs wk ∨
      (sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ 3 ≤ rs.2.val) := by
  constructor
  · intro win
    have safe := krk_force_weak_safe material turn ⟨4, win⟩
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact Or.inl goal.2
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · have every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u := by
        intro u step
        obtain ⟨r, legal, next⟩ := step_sound
          (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
        obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry legal next.1 next.2
        exact (strong_three_iff next.1 next.2 nextFar notCheck).mp (defended.2.2 r legal)
      rcases central_four_necessary material.1 rank low high far safe every with terminal | last | opposition
      · exact Or.inl ((kernel_mate_iff material turn far).mpr terminal)
      · exact Or.inr (Or.inl last)
      · exact Or.inr (Or.inr opposition)
  · rintro (mate | last | ⟨sx, sy, ry⟩)
    · exact mateWithin_mono (show MateWithin σ 0 q from ⟨turn, mate⟩) (by omega)
    · exact mateWithin_mono ((weak_two_iff material turn far).mpr (Or.inr last)) (by omega)
    · have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank]; omega)
      obtain ⟨u, step⟩ := opposition_nonempty rank low high sx sy ry
      obtain ⟨r, legal, _⟩ := step_sound
        (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
      apply mateWithin_defend turn ⟨r, legal⟩
      intro v reply
      obtain ⟨t, next, move⟩ := krk_safe_reply material turn safe reply
      obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry reply next.1 next.2
      exact (strong_three_iff next.1 next.2 nextFar notCheck).mpr
        (opposition_replies rank low high sx sy ry t move)

end EndgameChess.Rules.KRKFourPlyMiddle
