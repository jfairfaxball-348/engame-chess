import EndgameChess.Rules.KRKTwelveInteriorExact

namespace EndgameChess.Rules.KRKElevenEdge
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 300000

/-- Canonical edge king-point intersections with the evaluated ten-ply
five-compass region; no future winning predicate occurs. -/
def KingEntries (sk rs wk : Square) : Prop :=
  ∃ i : KRKElevenSlots.Kind, dInf sk (KRKElevenSlots.point i) = 1 ∧ KRKElevenSlots.point i ≠ rs ∧
    2 ≤ dInf (KRKElevenSlots.point i) wk ∧ KRKTenEdge.Region (KRKElevenSlots.point i) rs wk

def RookEntries (sk rs wk : Square) : Prop :=
  ∃ i : KRKElevenSlots.Kind, sk = KRKElevenSlots.point i ∧
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8, RookSees rs (a.target rs v) sk wk ∧
      a.target rs v ≠ sk ∧ a.target rs v ≠ wk ∧ KRKTenEdge.Region sk (a.target rs v) wk

def Eleven (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨ KingEntries sk rs wk ∨ RookEntries sk rs wk

theorem clear_iff {sk rs wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) :
    KRKElevenGeometry.Clear sk rs wk ↔ Eleven sk rs wk := by
  have edge : KRKEdgeDepth.depth wk = 0 := by dsimp [KRKEdgeDepth.depth]; omega
  have frameF (s : Square) : (KRKElevenSlots.frame wk).f s = s := by
    simp only [KRKElevenSlots.frame,edge,↓reduceIte]
    exact KRKFiveMiddle.normalize_f rank high s
  have frameR (s : Square) : (KRKElevenSlots.frame wk).r s = s := by
    simp only [KRKElevenSlots.frame,edge,↓reduceIte]
    exact KRKFiveMiddle.normalize_r rank high s
  simp only [KRKElevenGeometry.Clear,KRKElevenGeometry.KingPoints,KRKElevenGeometry.RookRays,
    Eleven,KingEntries,RookEntries,frameF,frameR,KRKTenGlobal.Region,edge,↓reduceIte,
    KRKFiveMiddle.normalize_f rank high]

theorem kernel_eleven_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) :
    MateWithin σ 11 q ↔ Eleven sk rs wk :=
  (KRKElevenGeometry.kernel_eleven_iff material turn far notCheck).trans (clear_iff rank high)

end EndgameChess.Rules.KRKElevenEdge
