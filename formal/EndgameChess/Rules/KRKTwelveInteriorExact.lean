import EndgameChess.Rules.KRKTwelveInnerExact
import EndgameChess.Rules.KRKTwelveDeepExact

namespace EndgameChess.Rules.KRKTwelveInteriorExact
open EndgameChess.KK KRKNativeFrame
open KRKEightInteriorExact (stripFrame strip_spec)
set_option maxHeartbeats 400000

def StripRegion (sk rs wk : Square) : Prop :=
  let g := stripFrame wk
  ((g.f wk).2.val = 1 ∧ KRKTwelveInnerExact.Region (g.f sk) (g.f rs)) ∨
  ((g.f wk).2.val = 2 ∧ KRKTwelveNearExact.Region (g.f sk) (g.f rs)) ∨
  ((g.f wk).2.val = 3 ∧ KRKTwelveCentralExact.Region (g.f sk) (g.f rs))

/-- Complete twelve-ply interior geometry, including the second corners. -/
def Region (sk rs wk : Square) : Prop :=
  if KRKEdgeDepth.depth wk = 1 then StripRegion sk rs wk else KRKTwelveDeepExact.Region sk rs wk

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < KRKEdgeDepth.depth wk) :
    MateWithin σ 12 q ↔ Region sk rs wk := by
  by_cases depth : KRKEdgeDepth.depth wk = 1
  · simp only [Region,depth,↓reduceIte]
    have spec := strip_spec depth
    let g := stripFrame wk
    change (g.f wk).1.val = 1 ∧ 1 ≤ (g.f wk).2.val ∧ (g.f wk).2.val ≤ 3 at spec
    have notMate : ¬MatedK q := by
      intro mate
      have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
      omega
    constructor
    · intro win
      have clear := (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp win
      have ys : (g.f wk).2.val = 1 ∨ (g.f wk).2.val = 2 ∨ (g.f wk).2.val = 3 := by omega
      rcases ys with one | two | three
      · have target : g.f wk = ((1 : Fin 8),1) := Prod.ext (Fin.ext spec.1) (Fin.ext one)
        exact Or.inl ⟨one,(KRKTwelveInnerExact.framed_clear_iff g target material.1 far).mp clear⟩
      · have target : g.f wk = ((1 : Fin 8),2) := Prod.ext (Fin.ext spec.1) (Fin.ext two)
        exact Or.inr (Or.inl ⟨two,(KRKTwelveNearExact.framed_clear_iff g target material.1 far).mp clear⟩)
      · have target : g.f wk = ((1 : Fin 8),3) := Prod.ext (Fin.ext spec.1) (Fin.ext three)
        exact Or.inr (Or.inr ⟨three,(KRKTwelveCentralExact.framed_clear_iff g target material.1 far).mp clear⟩)
    · intro region
      apply (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr
      rcases region with ⟨one,inner⟩ | ⟨two,near⟩ | ⟨three,central⟩
      · have target : g.f wk = ((1 : Fin 8),1) := Prod.ext (Fin.ext spec.1) (Fin.ext one)
        exact (KRKTwelveInnerExact.framed_clear_iff g target material.1 far).mpr inner
      · have target : g.f wk = ((1 : Fin 8),2) := Prod.ext (Fin.ext spec.1) (Fin.ext two)
        exact (KRKTwelveNearExact.framed_clear_iff g target material.1 far).mpr near
      · have target : g.f wk = ((1 : Fin 8),3) := Prod.ext (Fin.ext spec.1) (Fin.ext three)
        exact (KRKTwelveCentralExact.framed_clear_iff g target material.1 far).mpr central
  · simp only [Region,depth,↓reduceIte]
    exact KRKTwelveDeepExact.kernel_twelve_iff material turn far (by omega)

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < KRKEdgeDepth.depth wk) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔
      Region sk rs wk ∧ ¬KRKTenInteriorExact.Region sk rs wk := by
  constructor
  · rintro ⟨twelve,notEleven⟩
    refine ⟨(kernel_twelve_iff material turn far inside).mp twelve,?_⟩
    intro old
    have ten := (KRKTenInteriorExact.kernel_ten_iff material turn far inside).mpr old
    exact notEleven (mateWithin_mono ten (by decide))
  · rintro ⟨region,notOld⟩
    exact ⟨(kernel_twelve_iff material turn far inside).mpr region,fun eleven =>
      notOld ((KRKTenInteriorExact.kernel_ten_iff material turn far inside).mp
        (KRKTenGeometry.weak_eleven_ten material turn eleven))⟩

end EndgameChess.Rules.KRKTwelveInteriorExact
