import EndgameChess.Rules.KRKFourPlyEscape
import EndgameChess.Rules.KRKBound.Transport

namespace EndgameChess.Rules.KRKFourPlyEscape
open EndgameChess.KK KRKLastReply KRKImmediate KRKThreePly
set_option maxHeartbeats 1000000

private theorem three_map (g : BoardSym) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) (three : Three sk rs wk) :
    Three (g.f sk) (g.f rs) (g.f wk) := by
  let q := krkPos .white sk rs wk .white
  let r := krkPos .white (g.f sk) (g.f rs) (g.f wk) .white
  have material : IsKRK q .white sk rs wk := ⟨distinct, notKing, notRook, rfl⟩
  have mapped : IsKRK r .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr distinct, g.ne_iff.mpr notKing, g.ne_iff.mpr notRook, rfl⟩
  have win := (strong_three_iff material rfl far notCheck).mpr three
  have transported := krk_bound_transport g
    (show Matches q .white ⟨sk, rs, wk, true⟩ from ⟨material, rfl⟩) rfl
    (show Matches r .white ((⟨sk, rs, wk, true⟩ : KRKState).map g) from ⟨mapped, rfl⟩) win
  apply (strong_three_iff mapped rfl (by rwa [g.dInf_eq]) ?_).mp transported
  intro sees
  exact notCheck ((g.sees_iff _ _ _ _).mp sees)

private theorem every_map (g : BoardSym) {sk rs wk : Square} (distinct : sk ≠ rs)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) :
    ∀ u, StepM ⟨g.f sk, g.f rs, g.f wk, false⟩ ⟨g.f sk, g.f rs, u, true⟩ →
      Three (g.f sk) (g.f rs) u := by
  intro u step
  have back := step_map g step
  change StepM ⟨g.f (g.f sk), g.f (g.f rs), g.f (g.f wk), false⟩
    ⟨g.f (g.f sk), g.f (g.f rs), g.f u, true⟩ at back
  simp only [g.invol] at back
  have far : 2 ≤ dInf sk (g.f u) := by cases back with | lone _ _ h _ => exact h
  have notRook : rs ≠ g.f u := by cases back with | lone _ h _ _ => exact Ne.symm h
  have notCheck : ¬RookSees rs (g.f u) sk (g.f u) := by cases back with | lone _ _ _ h => exact h
  have notKing : sk ≠ g.f u := ne_of_dInf_pos (by omega)
  have mapped := three_map g distinct notKing notRook far notCheck (every (g.f u) back)
  simpa only [g.invol] using mapped

private theorem safe_map (g : BoardSym) {sk rs wk : Square} (safe : SafeRook sk rs wk) :
    SafeRook (g.f sk) (g.f rs) (g.f wk) := by
  simpa only [SafeRook, g.dInf_eq] using safe

private theorem west_escape {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (low : 1 ≤ wk.2.val) (high : wk.2.val ≤ 6)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) : False := by
  by_cases bottom : wk.2.val = 1
  · exact corner_escape file bottom far safe every
  by_cases top : wk.2.val = 6
  · exact corner_escape (sk := symY.f sk) (rs := symY.f rs) (wk := symY.f wk)
      (by simp [symY, file]) (by simp [symY, top])
      (by rwa [symY.dInf_eq]) (safe_map symY safe) (every_map symY distinct every)
  exact strip_escape file (by omega) (by omega) far safe every

private theorem side_escape {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1 ∨ wk.1.val = 6) (low : 1 ≤ wk.2.val) (high : wk.2.val ≤ 6)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) : False := by
  rcases file with west | east
  · exact west_escape distinct west low high far safe every
  · exact west_escape (sk := symX.f sk) (rs := symX.f rs) (wk := symX.f wk)
      (symX.ne_iff.mpr distinct) (by simp [symX, east]) low high
      (by rwa [symX.dInf_eq]) (safe_map symX safe) (every_map symX distinct every)

/-- An interior king at least two squares from all edges cannot have all
eight neighbours covered by a king and a safe rook. -/
theorem deep_prison_impossible {sk rs wk : Square}
    (xl : 2 ≤ wk.1.val) (xh : wk.1.val ≤ 5) (yl : 2 ≤ wk.2.val) (yh : wk.2.val ≤ 5)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t) : False := by
  let left : Fin 8 := ⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩
  let right : Fin 8 := ⟨wk.1.val + 1, by omega⟩
  let down : Fin 8 := ⟨wk.2.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.2.isLt⟩
  let up : Fin 8 := ⟨wk.2.val + 1, by omega⟩
  have a := covered_box (cover (left, down) (by simp [dInf, absDiff, left, down] <;> omega)
    (by simp [KRKEdgeDepth.depth, left, down] <;> omega))
  have b := covered_box (cover (left, up) (by simp [dInf, absDiff, left, up] <;> omega)
    (by simp [KRKEdgeDepth.depth, left, up] <;> omega))
  have c := covered_box (cover (right, down) (by simp [dInf, absDiff, right, down] <;> omega)
    (by simp [KRKEdgeDepth.depth, right, down] <;> omega))
  have d := covered_box (cover (right, up) (by simp [dInf, absDiff, right, up] <;> omega)
    (by simp [KRKEdgeDepth.depth, right, up] <;> omega))
  have e := covered_box (cover (left, wk.2) (by simp [dInf, absDiff, left] <;> omega)
    (by simp [KRKEdgeDepth.depth, left] <;> omega))
  have f := covered_box (cover (right, wk.2) (by simp [dInf, absDiff, right] <;> omega)
    (by simp [KRKEdgeDepth.depth, right] <;> omega))
  have h := covered_box (cover (wk.1, down) (by simp [dInf, absDiff, down] <;> omega)
    (by simp [KRKEdgeDepth.depth, down] <;> omega))
  have i := covered_box (cover (wk.1, up) (by simp [dInf, absDiff, up] <;> omega)
    (by simp [KRKEdgeDepth.depth, up] <;> omega))
  clear cover
  simp [left, right, down, up] at a b c d e f h i
  simp only [SafeRook, dInf, absDiff] at far safe
  by_cases rookLeft : rs.1.val + 1 = wk.1.val
  · omega
  · by_cases rookRight : rs.1.val = wk.1.val + 1
    · omega
    · omega

/-- Pure coordinate obstruction behind the new interior four-ply lower bound. -/
theorem interior_four_impossible {sk rs wk : Square} (distinct : sk ≠ rs)
    (inside : 0 < KRKEdgeDepth.depth wk) (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u) : False := by
  have bounds : 1 ≤ wk.1.val ∧ wk.1.val ≤ 6 ∧ 1 ≤ wk.2.val ∧ wk.2.val ≤ 6 := by
    simp only [KRKEdgeDepth.depth] at inside; omega
  by_cases file : wk.1.val = 1 ∨ wk.1.val = 6
  · exact side_escape distinct file bounds.2.2.1 bounds.2.2.2 far safe every
  by_cases rank : wk.2.val = 1 ∨ wk.2.val = 6
  · exact side_escape (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk)
      (symSwap.ne_iff.mpr distinct) rank bounds.1 bounds.2.1
      (by rwa [symSwap.dInf_eq]) (safe_map symSwap safe) (every_map symSwap distinct every)
  exact deep_prison_impossible (by omega) (by omega) (by omega) (by omega) far safe
    (fun t ht hi => interior_neighbour_covered safe ht hi every)

end EndgameChess.Rules.KRKFourPlyEscape
