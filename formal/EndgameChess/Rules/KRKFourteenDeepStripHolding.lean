import EndgameChess.Rules.KRKThirteenInteriorBarriers

namespace EndgameChess.Rules.KRKFourteenDeepStripHolding
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem near_corner_no_clear {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (2,3)) :
    ¬KRKFourteenGeometry.Clear sk rs (2,3) := by
  intro clear
  have safe := clear.1
  rcases KRKFourteenDeepStrip.prison far clear with
    ⟨sx,ys,ry⟩ | ⟨sx,sy,rx⟩ | ⟨sx,ys,rx,ry⟩ | ⟨sy,low,high,rx⟩
  · have notFile : rs.1.val ≠ 2 := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    have guard : KRKCornerWeakBand.Guard sk rs (2,3) (2,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry]
      dsimp; omega
    have evaluated := KRKThirteenInteriorBarriers.second_entry_necessary (clear.2.2 _ guard)
    simp only [square_eq_iff,Fin.ext_iff] at evaluated
    dsimp [dInf,absDiff] at evaluated
    omega
  · have notRow : rs.2.val ≠ 4 := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    have guard : KRKCornerWeakBand.Guard sk rs (2,3) (1,4) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
      dsimp; omega
    let g := Frame.ofSym symY
    have source := KRKThirteenGeometry.frame_map g apart
      (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2 (clear.2.2 _ guard)
    have kingEq : g.f sk = ((4 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext (by dsimp [g,Frame.ofSym,symY]; omega))
    have target : g.f ((1 : Fin 8),4) = ((1 : Fin 8),3) := rfl
    rw [kingEq,target] at source
    exact KRKThirteenInteriorBarriers.central_four_four_no_thirteen (by change rs.1.val = 2; exact rx) source
  · have guard : KRKCornerWeakBand.Guard sk rs (2,3) (2,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,rx,ry]
      dsimp; omega
    have evaluated := KRKThirteenInteriorBarriers.second_entry_necessary (clear.2.2 _ guard)
    simp only [square_eq_iff,Fin.ext_iff] at evaluated
    dsimp [dInf,absDiff] at evaluated
    omega
  · have notRow : rs.2.val ≠ 2 := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    have guard : KRKCornerWeakBand.Guard sk rs (2,3) (2,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
      dsimp; omega
    have evaluated := KRKThirteenInteriorBarriers.second_entry_necessary (clear.2.2 _ guard)
    simp only [square_eq_iff,Fin.ext_iff] at evaluated
    dsimp [dInf,absDiff] at evaluated
    have height : 4 ≤ rs.2.val := by omega
    have next : KRKCornerWeakBand.Guard sk rs (2,3) (1,2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
      dsimp; omega
    have kingEq : sk = (sk.1,(5 : Fin 8)) := Prod.ext rfl (Fin.ext sy)
    have child := clear.2.2 _ next
    rw [kingEq] at child
    exact KRKThirteenInteriorBarriers.near_upper_no_thirteen rx (by omega) child

def Belt (wk : Square) : Prop :=
  ((wk.1.val = 2 ∨ wk.1.val = 5) ∧ (wk.2.val = 3 ∨ wk.2.val = 4)) ∨
  ((wk.1.val = 3 ∨ wk.1.val = 4) ∧ (wk.2.val = 2 ∨ wk.2.val = 5))

private def beltFrame (wk : Square) : Frame :=
  if wk.1.val = 2 then (if wk.2.val = 3 then Frame.ofSym symId else Frame.ofSym symY)
  else if wk.1.val = 5 then (if wk.2.val = 3 then Frame.ofSym symX else Frame.ofSym symXY)
  else if wk.2.val = 2 then
    (if wk.1.val = 3 then Frame.ofSym symSwap else (Frame.ofSym symX).comp (Frame.ofSym symSwap))
  else if wk.1.val = 3 then (Frame.ofSym symY).comp (Frame.ofSym symSwap)
    else (Frame.ofSym symSwap).comp (Frame.ofSym symXY)

private theorem belt_target {wk : Square} (belt : Belt wk) : (beltFrame wk).f wk = ((2 : Fin 8),3) := by
  dsimp [Belt] at belt
  dsimp [beltFrame]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    rw [square_eq_iff] <;> dsimp [Frame.ofSym,Frame.comp,symId,symX,symY,symXY,symSwap] <;>
    simp only [show ((3 : Fin 8).val) = 3 from rfl] <;> omega

theorem belt_no_clear {sk rs wk : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk) (belt : Belt wk) :
    ¬KRKFourteenGeometry.Clear sk rs wk := by
  intro clear
  let g := beltFrame wk
  have target := belt_target belt
  have mapped := KRKFourteenGeometry.frame_map g apart clear
  have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
  rw [target] at mapped mappedFar
  exact near_corner_no_clear (g.ne_iff.mpr apart) mappedFar mapped

theorem deep_corner_necessary {sk rs wk : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk)
    (deep : 2 ≤ KRKEdgeDepth.depth wk) (clear : KRKFourteenGeometry.Clear sk rs wk) :
    KRKTwelveDeepExact.SecondCorner wk := by
  have bounds : 2 ≤ wk.1.val ∧ wk.1.val ≤ 5 ∧ 2 ≤ wk.2.val ∧ wk.2.val ≤ 5 := by
    dsimp [KRKEdgeDepth.depth] at deep
    omega
  by_cases corner : KRKTwelveDeepExact.SecondCorner wk
  · exact corner
  by_cases center : (wk.1.val = 3 ∨ wk.1.val = 4) ∧ (wk.2.val = 3 ∨ wk.2.val = 4)
  · exact False.elim (KRKFourteenDeep.central_no_clear apart far center.1 center.2 clear)
  have belt : Belt wk := by dsimp [KRKTwelveDeepExact.SecondCorner] at corner; dsimp [Belt]; omega
  exact False.elim (belt_no_clear apart far belt clear)

theorem kernel_deep_corner_necessary {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (deep : 2 ≤ KRKEdgeDepth.depth wk) (win : MateWithin σ 14 q) : KRKTwelveDeepExact.SecondCorner wk := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  exact deep_corner_necessary material.1 far deep ((KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).mp win)

end EndgameChess.Rules.KRKFourteenDeepStripHolding
