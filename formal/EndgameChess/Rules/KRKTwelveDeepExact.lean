import EndgameChess.Rules.KRKTwelveSecondCorner

namespace EndgameChess.Rules.KRKTwelveDeepExact
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
open KRKTenInterior (cornerSym)

theorem central_escape {sk rs wk : Square} (distinct : sk ≠ rs) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (xl : 2 ≤ wk.1.val) (xh : wk.1.val ≤ 5)
    (yl : 2 ≤ wk.2.val) (yh : wk.2.val ≤ 5)
    (central : (3 ≤ wk.1.val ∧ wk.1.val ≤ 4) ∨ (3 ≤ wk.2.val ∧ wk.2.val ≤ 4)) :
    ¬KRKTwelveGeometry.Clear sk rs wk := by
  intro clear
  let left : Fin 8 := ⟨wk.1.val-1,by omega⟩
  let right : Fin 8 := ⟨wk.1.val+1,by omega⟩
  let down : Fin 8 := ⟨wk.2.val-1,by omega⟩
  let up : Fin 8 := ⟨wk.2.val+1,by omega⟩
  have a := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (left,wk.2))
    (by dsimp [left,dInf,absDiff]; omega)
    (by dsimp [left,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  have b := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (right,wk.2))
    (by dsimp [right,dInf,absDiff]; omega)
    (by dsimp [right,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  have c := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (wk.1,down))
    (by dsimp [down,dInf,absDiff]; omega)
    (by dsimp [down,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  have d := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (wk.1,up))
    (by dsimp [up,dInf,absDiff]; omega)
    (by dsimp [up,KRKEdgeDepth.depth,KRKEightCentralStrip.MiddleStrip]; omega))
  clear clear
  dsimp [left,right,down,up] at a b c d
  simp only [dInf,absDiff] at far
  simp only [ne_iff_coords] at notRook
  omega

def SecondCorner (wk : Square) : Prop :=
  (wk.1.val = 2 ∨ wk.1.val = 5) ∧ (wk.2.val = 2 ∨ wk.2.val = 5)

def Region (sk rs wk : Square) : Prop :=
  SecondCorner wk ∧
    KRKTwelveSecondCorner.Region ((cornerSym wk).f sk) ((cornerSym wk).f rs)

theorem corner_target {wk : Square} (corner : SecondCorner wk) :
    (Frame.ofSym (cornerSym wk)).f wk = ((2 : Fin 8),2) := by
  by_cases x : wk.1.val = 2 <;> by_cases y : wk.2.val = 2 <;>
    simp only [cornerSym,x,y,↓reduceIte,Frame.ofSym] <;>
    rw [square_eq_iff] <;> dsimp [SecondCorner,symId,symX,symY,symXY] at corner ⊢ <;> omega

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (deep : 2 ≤ KRKEdgeDepth.depth wk) : MateWithin σ 12 q ↔ Region sk rs wk := by
  have bounds : 2 ≤ wk.1.val ∧ wk.1.val ≤ 5 ∧ 2 ≤ wk.2.val ∧ wk.2.val ≤ 5 := by
    dsimp [KRKEdgeDepth.depth] at deep
    omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  constructor
  · intro win
    have clear := (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp win
    have notCentral : ¬((3 ≤ wk.1.val ∧ wk.1.val ≤ 4) ∨ (3 ≤ wk.2.val ∧ wk.2.val ≤ 4)) := by
      intro central
      exact central_escape material.1 material.2.2.1 far bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 central clear
    have corner : SecondCorner wk := by dsimp [SecondCorner]; omega
    let g := Frame.ofSym (cornerSym wk)
    have target := corner_target corner
    have mapped := KRKTwelveGeometry.frame_map g material.1 clear
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    rw [target] at mapped mappedFar
    exact ⟨corner,KRKTwelveSecondCorner.necessary (g.ne_iff.mpr material.1) mappedFar mapped⟩
  · rintro ⟨corner,region⟩
    let g := Frame.ofSym (cornerSym wk)
    have target := corner_target corner
    have mapped := KRKTwelveSecondCorner.sufficient region
    have shaped : KRKTwelveGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKTwelveGeometry.frame_map g.inverse (g.ne_iff.mpr material.1) shaped
    apply (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr
    simpa only [Frame.inverse,g.left_inv] using back

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (deep : 2 ≤ KRKEdgeDepth.depth wk) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region sk rs wk := by
  have notTen : ¬MateWithin σ 10 q := by
    intro ten
    have shallow := KRKTenInterior.weak_ten_depth_le_one material turn far ten
    omega
  exact ⟨fun h => (kernel_twelve_iff material turn far deep).mp h.1,fun region =>
    ⟨(kernel_twelve_iff material turn far deep).mpr region,
      fun eleven => notTen (KRKTenGeometry.weak_eleven_ten material turn eleven)⟩⟩

end EndgameChess.Rules.KRKTwelveDeepExact
