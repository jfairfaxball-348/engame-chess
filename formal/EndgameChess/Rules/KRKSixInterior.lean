import EndgameChess.Rules.KRKFiveMiddle
import EndgameChess.Rules.KRKCastleSix

namespace EndgameChess.Rules.KRKSixInterior
open EndgameChess.KK KRKFourPlyEscape
set_option maxHeartbeats 500000

/-- In the noncorner first interior strip, the outward reply cannot belong
to the complete strong five-ply region. No incoming-history assumption is used. -/
theorem strip_escape {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (low : 2 ≤ wk.2.val) (high : wk.2.val ≤ 5)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) : False := by
  have cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t :=
    fun t distance inside => KRKCastleSix.interior_covered safe distance inside every
  obtain ⟨sx,sy,rx⟩ := strip_prison file low high far safe cover
  have separated : rs.2.val + 2 ≤ wk.2.val ∨ wk.2.val + 2 ≤ rs.2.val := by
    simp only [SafeRook,dInf,absDiff,file,sx,sy,rx] at safe
    omega
  let u : Square := (0,wk.2)
  have distance : dInf wk u = 1 := by simp [u,dInf,absDiff,file]
  have notRook : u ≠ rs := by rw [ne_iff_coords]; dsimp [u]; omega
  have postFar : 2 ≤ dInf sk u := by simp only [u,dInf,absDiff,sx]; omega
  have notCheck : ¬RookSees rs u sk u := by
    intro seen
    have line := seen.1.2
    dsimp [RookLine,u] at line
    omega
  have step := StepM.lone distance notRook postFar notCheck
  have five := every u step
  have notKing : sk ≠ u := ne_of_dInf_pos (by omega)
  have swapped := KRKFiveGeometry.map symSwap distinct notKing notRook.symm postFar notCheck five
  have mappedCheck : ¬RookSees (symSwap.f rs) (symSwap.f u) (symSwap.f sk) (symSwap.f u) :=
    fun seen => notCheck ((symSwap.sees_iff _ _ _ _).mp seen)
  have bottom := (KRKFiveMiddle.bottom_clear_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f u)
    (by rfl) (by dsimp [symSwap,u]; exact low) (by dsimp [symSwap,u]; exact high)
    (symSwap.ne_iff.mpr distinct) (symSwap.ne_iff.mpr notKing) (symSwap.ne_iff.mpr notRook.symm)
    (by rwa [symSwap.dInf_eq]) mappedCheck).mp swapped
  have forced := (KRKFiveMiddle.low_rook_bottom_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f u)
    (by dsimp [symSwap,u]; exact low) (by dsimp [symSwap,u]; exact high) (by dsimp [symSwap]; omega)).mp bottom
  have impossible := forced.1
  dsimp [symSwap] at impossible
  omega

private theorem every_map (g : BoardSym) {sk rs wk : Square} (distinct : sk ≠ rs)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → KRKFiveGeometry.Clear sk rs u) :
    ∀ u, StepM ⟨g.f sk, g.f rs, g.f wk, false⟩ ⟨g.f sk, g.f rs, u, true⟩ →
      KRKFiveGeometry.Clear (g.f sk) (g.f rs) u := by
  intro u step
  have back := step_map g step
  change StepM ⟨g.f (g.f sk), g.f (g.f rs), g.f (g.f wk), false⟩
    ⟨g.f (g.f sk), g.f (g.f rs), g.f u, true⟩ at back
  simp only [g.invol] at back
  have far : 2 ≤ dInf sk (g.f u) := by cases back with | lone _ _ h _ => exact h
  have notRook : rs ≠ g.f u := by cases back with | lone _ h _ _ => exact Ne.symm h
  have notCheck : ¬RookSees rs (g.f u) sk (g.f u) := by cases back with | lone _ _ _ h => exact h
  have notKing : sk ≠ g.f u := ne_of_dInf_pos (by omega)
  have mapped := KRKFiveGeometry.map g distinct notKing notRook far notCheck (every (g.f u) back)
  simpa only [g.invol] using mapped

private theorem safe_map (g : BoardSym) {sk rs wk : Square} (safe : SafeRook sk rs wk) :
    SafeRook (g.f sk) (g.f rs) (g.f wk) := by
  simpa only [SafeRook, g.dInf_eq] using safe


private theorem side_strip_escape {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1 ∨ wk.1.val = 6) (low : 2 ≤ wk.2.val) (high : wk.2.val ≤ 5)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) : False := by
  rcases file with left | right
  · exact strip_escape distinct left low high far safe every
  · exact strip_escape (sk := symX.f sk) (rs := symX.f rs) (wk := symX.f wk)
      (symX.ne_iff.mpr distinct) (by dsimp [symX]; omega) low high
      (by rwa [symX.dInf_eq]) (safe_map symX safe) (every_map symX distinct every)

def InnerCorner (wk : Square) : Prop :=
  (wk.1.val = 1 ∨ wk.1.val = 6) ∧ (wk.2.val = 1 ∨ wk.2.val = 6)

/-- Among interior weak roots, only the four first-band corner squares
can possibly support six-ply forcing. These four cases remain to be resolved. -/
theorem interior_corner_necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (inside : 0 < KRKEdgeDepth.depth wk) (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) : InnerCorner wk := by
  have bounds : 1 ≤ wk.1.val ∧ wk.1.val ≤ 6 ∧ 1 ≤ wk.2.val ∧ wk.2.val ≤ 6 := by
    simp only [KRKEdgeDepth.depth] at inside; omega
  by_cases file : wk.1.val = 1 ∨ wk.1.val = 6
  · by_cases rank : wk.2.val = 1 ∨ wk.2.val = 6
    · exact ⟨file,rank⟩
    · exact False.elim (side_strip_escape distinct file (by omega) (by omega) far safe every)
  by_cases rank : wk.2.val = 1 ∨ wk.2.val = 6
  · apply False.elim
    exact side_strip_escape (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk)
      (symSwap.ne_iff.mpr distinct) rank (by dsimp [symSwap]; omega) (by dsimp [symSwap]; omega)
      (by rwa [symSwap.dInf_eq]) (safe_map symSwap safe) (every_map symSwap distinct every)
  apply False.elim
  exact deep_prison_impossible (by omega) (by omega) (by omega) (by omega) far safe
    (fun t distance inside => KRKCastleSix.interior_covered safe distance inside every)

theorem weak_six_interior_corner {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (inside : 0 < KRKEdgeDepth.depth wk) (win : MateWithin σ 6 q) : InnerCorner wk := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  have geometry := (KRKSixGeometry.kernel_six_iff material turn notMate).mp win
  exact interior_corner_necessary material.1 inside far geometry.1
    (fun t step => geometry.2.2 t (KRKCornerWeakBand.step_guard step))

end EndgameChess.Rules.KRKSixInterior
