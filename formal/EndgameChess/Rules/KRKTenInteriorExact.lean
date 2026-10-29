import EndgameChess.Rules.KRKTenInner

namespace EndgameChess.Rules.KRKTenInteriorExact
open EndgameChess.KK KRKNativeFrame
open KRKEightInteriorExact (stripFrame strip_spec)
set_option maxHeartbeats 400000

/-- Entire interior ten-ply region, using two fixed destination geometries. -/
def Region (sk rs wk : Square) : Prop :=
  KRKEdgeDepth.depth wk = 1 ∧
    let g := stripFrame wk
    ((g.f wk).2.val = 1 ∧ KRKTenInner.Region (g.f sk) (g.f rs)) ∨
    ((g.f wk).2.val = 2 ∧ KRKTenNearStrip.Region (g.f sk) (g.f rs))

theorem kernel_ten_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < KRKEdgeDepth.depth wk) :
    MateWithin σ 10 q ↔ Region sk rs wk := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  constructor
  · intro eight
    have shallow := KRKTenInterior.weak_ten_depth_le_one material turn far eight
    have depth : KRKEdgeDepth.depth wk = 1 := by omega
    have spec := strip_spec depth
    let g := stripFrame wk
    change (g.f wk).1.val = 1 ∧ 1 ≤ (g.f wk).2.val ∧ (g.f wk).2.val ≤ 3 at spec
    have clear := (KRKTenGeometry.kernel_ten_iff material turn notMate).mp eight
    have mapped := KRKTenGeometry.frame_map g material.1 clear
    have ys : (g.f wk).2.val = 1 ∨ (g.f wk).2.val = 2 ∨ (g.f wk).2.val = 3 := by omega
    refine ⟨depth,?_⟩
    rcases ys with one | two | three
    · have target : g.f wk = ((1 : Fin 8),1) := Prod.ext (Fin.ext spec.1) (Fin.ext one)
      exact Or.inl ⟨one,(KRKTenInner.framed_clear_iff g target material.1 far).mp clear⟩
    · have target : g.f wk = ((1 : Fin 8),2) := Prod.ext (Fin.ext spec.1) (Fin.ext two)
      exact Or.inr ⟨two,(KRKTenNearStrip.framed_clear_iff g target material.1 far).mp clear⟩
    · exact False.elim (KRKTenCentralStrip.file_one_not_clear spec.1 (by omega) (by omega)
        (g.ne_iff.mpr material.1)
        (by rw [g.distance]; exact far) mapped)
  · rintro ⟨depth,region⟩
    have spec := strip_spec depth
    let g := stripFrame wk
    change (g.f wk).1.val = 1 ∧ 1 ≤ (g.f wk).2.val ∧ (g.f wk).2.val ≤ 3 at spec
    apply (KRKTenGeometry.kernel_ten_iff material turn notMate).mpr
    rcases region with ⟨one,inner⟩ | ⟨two,near⟩
    · have target : g.f wk = ((1 : Fin 8),1) := Prod.ext (Fin.ext spec.1) (Fin.ext one)
      exact (KRKTenInner.framed_clear_iff g target material.1 far).mpr inner
    · have target : g.f wk = ((1 : Fin 8),2) := Prod.ext (Fin.ext spec.1) (Fin.ext two)
      exact (KRKTenNearStrip.framed_clear_iff g target material.1 far).mpr near

theorem kernel_exact_ten {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < KRKEdgeDepth.depth wk) :
    (MateWithin σ 10 q ∧ ¬MateWithin σ 9 q) ↔
      Region sk rs wk ∧ ¬KRKEightInteriorExact.Region sk rs wk := by
  constructor
  · rintro ⟨eight,notSeven⟩
    refine ⟨(kernel_ten_iff material turn far inside).mp eight,?_⟩
    intro sixRegion
    have six := (KRKEightInteriorExact.kernel_eight_iff material turn far inside).mpr sixRegion
    exact notSeven (mateWithin_mono six (by decide))
  · rintro ⟨region,notSix⟩
    refine ⟨(kernel_ten_iff material turn far inside).mpr region,?_⟩
    intro seven
    exact notSix ((KRKEightInteriorExact.kernel_eight_iff material turn far inside).mp
      (KRKEightGeometry.weak_nine_eight material turn seven))


end EndgameChess.Rules.KRKTenInteriorExact
