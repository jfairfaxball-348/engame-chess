import EndgameChess.Rules.KRKFourteenSecondCornerExact

namespace EndgameChess.Rules.KRKFourteenDeepExact
open EndgameChess.KK KRKNativeFrame
open KRKTenInterior (cornerSym)
open KRKTwelveDeepExact (SecondCorner corner_target)
set_option maxHeartbeats 500000

def Region (sk rs wk : Square) : Prop :=
  SecondCorner wk ∧ KRKFourteenSecondCornerExact.Region ((cornerSym wk).f sk) ((cornerSym wk).f rs)

def FreshHorizontal (sk rs : Square) : Prop :=
  sk.1.val = 4 ∧ sk.2.val = 2 ∧ rs.2.val = 3 ∧ 3 ≤ rs.1.val

def Fresh (sk rs : Square) : Prop := FreshHorizontal sk rs ∨ FreshHorizontal (symSwap.f sk) (symSwap.f rs)

def FreshRegion (sk rs wk : Square) : Prop :=
  SecondCorner wk ∧ Fresh ((cornerSym wk).f sk) ((cornerSym wk).f rs)

theorem fresh_iff {sk rs : Square} :
    KRKFourteenSecondCornerExact.Region sk rs ∧ ¬KRKTwelveSecondCorner.Region sk rs ↔ Fresh sk rs := by
  dsimp [KRKFourteenSecondCornerExact.Region,KRKFourteenSecondCornerExact.Horizontal,
    KRKTwelveSecondCorner.Region,KRKTwelveSecondCorner.Horizontal,Fresh,FreshHorizontal,symSwap]
  omega

theorem kernel_fourteen_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (deep : 2 ≤ KRKEdgeDepth.depth wk) : MateWithin σ 14 q ↔ Region sk rs wk := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  constructor
  · intro win
    have clear := (KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).mp win
    have corner := KRKFourteenDeepStripHolding.deep_corner_necessary material.1 far deep clear
    let g := Frame.ofSym (cornerSym wk)
    have target := corner_target corner
    have mapped := KRKFourteenGeometry.frame_map g material.1 clear
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    rw [target] at mapped mappedFar
    exact ⟨corner,KRKFourteenSecondCornerExact.necessary (g.ne_iff.mpr material.1) mappedFar mapped⟩
  · rintro ⟨corner,region⟩
    let g := Frame.ofSym (cornerSym wk)
    have target := corner_target corner
    have mapped := KRKFourteenSecondCornerExact.sufficient (g.ne_iff.mpr material.1) region
    have shaped : KRKFourteenGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKFourteenGeometry.frame_map g.inverse (g.ne_iff.mpr material.1) shaped
    apply (KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).mpr
    simpa only [Frame.inverse,g.left_inv] using back

theorem kernel_exact_fourteen_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (deep : 2 ≤ KRKEdgeDepth.depth wk) :
    (MateWithin σ 14 q ∧ ¬MateWithin σ 13 q) ↔ Region sk rs wk ∧ ¬KRKTwelveDeepExact.Region sk rs wk := by
  constructor
  · rintro ⟨fourteen,notThirteen⟩
    refine ⟨(kernel_fourteen_iff material turn far deep).mp fourteen,?_⟩
    intro old
    exact notThirteen (mateWithin_mono ((KRKTwelveDeepExact.kernel_twelve_iff material turn far deep).mpr old) (by decide))
  · rintro ⟨region,notOld⟩
    exact ⟨(kernel_fourteen_iff material turn far deep).mpr region,fun thirteen =>
      notOld ((KRKTwelveDeepExact.kernel_twelve_iff material turn far deep).mp
        (KRKTwelveGeometry.weak_thirteen_twelve material turn thirteen))⟩

theorem kernel_exact_fourteen {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (deep : 2 ≤ KRKEdgeDepth.depth wk) :
    (MateWithin σ 14 q ∧ ¬MateWithin σ 13 q) ↔ FreshRegion sk rs wk := by
  rw [kernel_exact_fourteen_iff material turn far deep]
  constructor
  · rintro ⟨⟨corner,region⟩,notOld⟩
    exact ⟨corner,fresh_iff.mp ⟨region,fun old => notOld ⟨corner,old⟩⟩⟩
  · rintro ⟨corner,fresh⟩
    have pair := fresh_iff.mpr fresh
    exact ⟨⟨corner,pair.1⟩,fun old => pair.2 old.2⟩

end EndgameChess.Rules.KRKFourteenDeepExact
