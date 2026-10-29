import EndgameChess.Rules.KRKEightInner

namespace EndgameChess.Rules.KRKEightInteriorExact
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

/-- Canonical first-strip coordinates. This transforms geometry only. -/
def stripFrame (wk : Square) : Frame :=
  if wk.1.val = 1 then
    if wk.2.val ≤ 3 then Frame.ofSym symId else Frame.ofSym symY
  else if wk.1.val = 6 then
    if wk.2.val ≤ 3 then Frame.ofSym symX else Frame.ofSym symXY
  else if wk.2.val = 1 then
    if wk.1.val ≤ 3 then Frame.ofSym symSwap else (Frame.ofSym symSwap).comp (Frame.ofSym symY)
  else if wk.1.val ≤ 3 then (Frame.ofSym symSwap).comp (Frame.ofSym symX)
    else (Frame.ofSym symSwap).comp (Frame.ofSym symXY)

theorem strip_spec {wk : Square} (depth : KRKEdgeDepth.depth wk = 1) :
    ((stripFrame wk).f wk).1.val = 1 ∧
      1 ≤ ((stripFrame wk).f wk).2.val ∧ ((stripFrame wk).f wk).2.val ≤ 3 := by
  dsimp [KRKEdgeDepth.depth] at depth
  dsimp [stripFrame]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    dsimp [Frame.ofSym,Frame.comp,symId,symX,symY,symXY,symSwap] <;> omega

/-- Entire interior eight-ply region, using two fixed destination geometries. -/
def Region (sk rs wk : Square) : Prop :=
  KRKEdgeDepth.depth wk = 1 ∧
    let g := stripFrame wk
    ((g.f wk).2.val = 1 ∧ KRKEightInner.Region (g.f sk) (g.f rs)) ∨
    ((g.f wk).2.val = 2 ∧ KRKEightStrip.Region (g.f sk) (g.f rs) (1,2))

theorem kernel_eight_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < KRKEdgeDepth.depth wk) :
    MateWithin σ 8 q ↔ Region sk rs wk := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  constructor
  · intro eight
    have shallow := KRKEightInterior.weak_eight_depth_le_one material turn far eight
    have depth : KRKEdgeDepth.depth wk = 1 := by omega
    have spec := strip_spec depth
    let g := stripFrame wk
    change (g.f wk).1.val = 1 ∧ 1 ≤ (g.f wk).2.val ∧ (g.f wk).2.val ≤ 3 at spec
    have clear := (KRKEightGeometry.kernel_eight_iff material turn notMate).mp eight
    have mapped := KRKCastleEight.frame_map g material.1 clear
    have ys : (g.f wk).2.val = 1 ∨ (g.f wk).2.val = 2 ∨ (g.f wk).2.val = 3 := by omega
    refine ⟨depth,?_⟩
    rcases ys with one | two | three
    · have target : g.f wk = ((1 : Fin 8),1) := Prod.ext (Fin.ext spec.1) (Fin.ext one)
      exact Or.inl ⟨one,(KRKEightInner.framed_clear_iff g target material.1 far).mp clear⟩
    · have target : g.f wk = ((1 : Fin 8),2) := Prod.ext (Fin.ext spec.1) (Fin.ext two)
      exact Or.inr ⟨two,(KRKEightNearStrip.framed_clear_iff g target material.1 far).mp clear⟩
    · exact False.elim (KRKEightCentralStrip.not_clear spec.1 (by omega) (by omega)
        (g.ne_iff.mpr material.1) (g.ne_iff.mpr material.2.2.1)
        (by rw [g.distance]; exact far) mapped)
  · rintro ⟨depth,region⟩
    have spec := strip_spec depth
    let g := stripFrame wk
    change (g.f wk).1.val = 1 ∧ 1 ≤ (g.f wk).2.val ∧ (g.f wk).2.val ≤ 3 at spec
    apply (KRKEightGeometry.kernel_eight_iff material turn notMate).mpr
    rcases region with ⟨one,inner⟩ | ⟨two,near⟩
    · have target : g.f wk = ((1 : Fin 8),1) := Prod.ext (Fin.ext spec.1) (Fin.ext one)
      exact (KRKEightInner.framed_clear_iff g target material.1 far).mpr inner
    · have target : g.f wk = ((1 : Fin 8),2) := Prod.ext (Fin.ext spec.1) (Fin.ext two)
      exact (KRKEightNearStrip.framed_clear_iff g target material.1 far).mpr near

theorem kernel_exact_eight {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < KRKEdgeDepth.depth wk) :
    (MateWithin σ 8 q ∧ ¬MateWithin σ 7 q) ↔
      Region sk rs wk ∧ ¬KRKSixInwardCorner.GlobalRegion sk rs wk := by
  constructor
  · rintro ⟨eight,notSeven⟩
    refine ⟨(kernel_eight_iff material turn far inside).mp eight,?_⟩
    intro sixRegion
    have six := (KRKSixInwardCorner.global_kernel_six_iff material turn far inside).mpr sixRegion
    exact notSeven (mateWithin_mono six (by decide))
  · rintro ⟨region,notSix⟩
    refine ⟨(kernel_eight_iff material turn far inside).mpr region,?_⟩
    intro seven
    exact notSix ((KRKSixInwardCorner.global_kernel_six_iff material turn far inside).mp
      (KRKSixGeometry.weak_seven_six material turn seven))

end EndgameChess.Rules.KRKEightInteriorExact
