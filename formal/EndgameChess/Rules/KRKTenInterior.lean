import EndgameChess.Rules.KRKTenSecondCorner

namespace EndgameChess.Rules.KRKTenInterior
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem central_escape {sk rs wk : Square} (distinct : sk ≠ rs) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (xl : 2 ≤ wk.1.val) (xh : wk.1.val ≤ 5)
    (yl : 2 ≤ wk.2.val) (yh : wk.2.val ≤ 5)
    (central : (3 ≤ wk.1.val ∧ wk.1.val ≤ 4) ∨ (3 ≤ wk.2.val ∧ wk.2.val ≤ 4)) :
    ¬KRKTenGeometry.Clear sk rs wk := by
  intro clear
  let left : Fin 8 := ⟨wk.1.val-1,by omega⟩
  let right : Fin 8 := ⟨wk.1.val+1,by omega⟩
  let down : Fin 8 := ⟨wk.2.val-1,by omega⟩
  let up : Fin 8 := ⟨wk.2.val+1,by omega⟩
  have a := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (left,wk.2))
    (by dsimp [left,dInf,absDiff]; omega)
    (by dsimp [left,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  have b := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (right,wk.2))
    (by dsimp [right,dInf,absDiff]; omega)
    (by dsimp [right,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  have c := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (wk.1,down))
    (by dsimp [down,dInf,absDiff]; omega)
    (by dsimp [down,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  have d := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (wk.1,up))
    (by dsimp [up,dInf,absDiff]; omega)
    (by dsimp [up,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  clear clear
  dsimp [left,right,down,up] at a b c d
  simp only [dInf,absDiff] at far
  simp only [ne_iff_coords] at notRook
  omega

def cornerSym (wk : Square) : BoardSym :=
  if wk.1.val = 2 then (if wk.2.val = 2 then symId else symY)
  else (if wk.2.val = 2 then symX else symXY)

theorem deep_not_clear {sk rs wk : Square} (distinct : sk ≠ rs) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (deep : 2 ≤ KRKEdgeDepth.depth wk) : ¬KRKTenGeometry.Clear sk rs wk := by
  have bounds : 2 ≤ wk.1.val ∧ wk.1.val ≤ 5 ∧ 2 ≤ wk.2.val ∧ wk.2.val ≤ 5 := by
    dsimp [KRKEdgeDepth.depth] at deep
    omega
  by_cases central : (3 ≤ wk.1.val ∧ wk.1.val ≤ 4) ∨ (3 ≤ wk.2.val ∧ wk.2.val ≤ 4)
  · exact central_escape distinct notRook far bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 central
  · have target : (Frame.ofSym (cornerSym wk)).f wk = ((2 : Fin 8),2) := by
      by_cases x : wk.1.val = 2 <;> by_cases y : wk.2.val = 2 <;>
        simp only [cornerSym,x,y,↓reduceIte,Frame.ofSym] <;>
        rw [square_eq_iff] <;> dsimp [symId,symX,symY,symXY] <;> omega
    exact KRKTenSecondCorner.framed_not_clear _ target distinct far

theorem weak_ten_depth_le_one {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (win : MateWithin σ 10 q) : KRKEdgeDepth.depth wk ≤ 1 := by
  by_cases shallow : KRKEdgeDepth.depth wk ≤ 1
  · exact shallow
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  exact False.elim (deep_not_clear material.1 material.2.2.1 far (by omega)
    ((KRKTenGeometry.kernel_ten_iff material turn notMate).mp win))

end EndgameChess.Rules.KRKTenInterior
