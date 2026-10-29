import EndgameChess.Rules.KRKTenInteriorExact

namespace EndgameChess.Rules.KRKNineEdge
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 300000

/-- Canonical edge king-point intersections with the evaluated eight-ply
five-compass region; no future winning predicate occurs. -/
def KingEntries (sk rs wk : Square) : Prop :=
  ∃ i : KRKNineSlots.Kind, dInf sk (KRKNineSlots.point i) = 1 ∧ KRKNineSlots.point i ≠ rs ∧
    2 ≤ dInf (KRKNineSlots.point i) wk ∧ KRKEightEdge.Region (KRKNineSlots.point i) rs wk

def RookEntries (sk rs wk : Square) : Prop :=
  ∃ i : KRKNineSlots.Kind, sk = KRKNineSlots.point i ∧
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8, RookSees rs (a.target rs v) sk wk ∧
      a.target rs v ≠ sk ∧ a.target rs v ≠ wk ∧ KRKEightEdge.Region sk (a.target rs v) wk

def Nine (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨ KingEntries sk rs wk ∨ RookEntries sk rs wk

theorem clear_iff {sk rs wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) :
    KRKNineGeometry.Clear sk rs wk ↔ Nine sk rs wk := by
  have edge : KRKEdgeDepth.depth wk = 0 := by dsimp [KRKEdgeDepth.depth]; omega
  have frameF (s : Square) : (KRKNineSlots.frame wk).f s = s := by
    simp only [KRKNineSlots.frame,edge,↓reduceIte]
    exact KRKFiveMiddle.normalize_f rank high s
  have frameR (s : Square) : (KRKNineSlots.frame wk).r s = s := by
    simp only [KRKNineSlots.frame,edge,↓reduceIte]
    exact KRKFiveMiddle.normalize_r rank high s
  simp only [KRKNineGeometry.Clear,KRKNineGeometry.KingPoints,KRKNineGeometry.RookRays,
    Nine,KingEntries,RookEntries,frameF,frameR,KRKEightGlobal.Region,edge,↓reduceIte,
    KRKFiveMiddle.normalize_f rank high]

theorem kernel_nine_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) :
    MateWithin σ 9 q ↔ Nine sk rs wk :=
  (KRKNineGeometry.kernel_nine_iff material turn far notCheck).trans (clear_iff rank high)

end EndgameChess.Rules.KRKNineEdge
