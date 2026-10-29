import EndgameChess.Rules.KRKFourteenGeometry

namespace EndgameChess.Rules.KRKFourteenDeep
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem bad_neighbour_covered {sk rs wk t : Square} (clear : KRKFourteenGeometry.Clear sk rs wk)
    (distance : dInf wk t = 1) (deep : 2 ≤ KRKEdgeDepth.depth t)
    (notCorner : ¬KRKTwelveDeepExact.SecondCorner t) : Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have notRook : t ≠ rs := by
    intro equal
    rcases clear.1 with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have guard : KRKCornerWeakBand.Guard sk rs wk t := ⟨distance,notRook,by omega,fun seen => line seen.1⟩
  exact False.elim (notCorner (KRKFourteenGeometry.thirteen_deep_corner deep (clear.2.2 _ guard)))

theorem central_three_no_clear {sk rs : Square} (far : 2 ≤ dInf sk (3,3)) :
    ¬KRKFourteenGeometry.Clear sk rs (3,3) := by
  intro clear
  have a := covered_box (bad_neighbour_covered clear (t := ((2 : Fin 8),3)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have b := covered_box (bad_neighbour_covered clear (t := ((2 : Fin 8),4)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have c := covered_box (bad_neighbour_covered clear (t := ((3 : Fin 8),2)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have d := covered_box (bad_neighbour_covered clear (t := ((3 : Fin 8),4)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have e := covered_box (bad_neighbour_covered clear (t := ((4 : Fin 8),2)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have f := covered_box (bad_neighbour_covered clear (t := ((4 : Fin 8),3)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have g := covered_box (bad_neighbour_covered clear (t := ((4 : Fin 8),4)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  dsimp at a b c d e f g
  dsimp [dInf,absDiff] at far
  omega

theorem central_no_clear {sk rs wk : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk)
    (x : wk.1.val = 3 ∨ wk.1.val = 4) (y : wk.2.val = 3 ∨ wk.2.val = 4) :
    ¬KRKFourteenGeometry.Clear sk rs wk := by
  intro clear
  let s := if wk.1.val = 3 then (if wk.2.val = 3 then symId else symY)
    else (if wk.2.val = 3 then symX else symXY)
  let g := Frame.ofSym s
  have target : g.f wk = ((3 : Fin 8),3) := by
    by_cases a : wk.1.val = 3 <;> by_cases b : wk.2.val = 3 <;>
      simp only [g,s,a,b,↓reduceIte,Frame.ofSym] <;>
      rw [square_eq_iff] <;> dsimp [symId,symX,symY,symXY] <;> omega
  have mapped := KRKFourteenGeometry.frame_map g apart clear
  have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
  rw [target] at mapped mappedFar
  exact central_three_no_clear mappedFar mapped

theorem kernel_central_no_fourteen {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (x : wk.1.val = 3 ∨ wk.1.val = 4) (y : wk.2.val = 3 ∨ wk.2.val = 4) : ¬MateWithin σ 14 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    dsimp [KRKEdgeDepth.depth] at zero
    omega
  exact fun win => central_no_clear material.1 far x y ((KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).mp win)

end EndgameChess.Rules.KRKFourteenDeep
