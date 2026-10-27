import EndgameChess.Rules.KRKFiveMiddle
import EndgameChess.Rules.KRKCastleSix

namespace EndgameChess.Rules.KRKSixMiddle
open EndgameChess.KK KRKFiveMiddle KRKFourPlyEscape KRKMateGeometry
set_option maxHeartbeats 400000

theorem covered_or_five {sk rs wk t : Square} (distinct : sk ≠ rs)
    (safe : SafeRook sk rs wk) (distance : dInf wk t = 1)
    (rank : t.2.val = 0) (low : 2 ≤ t.1.val) (high : t.1.val ≤ 5)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) :
    (sk.1.val ≤ t.1.val + 1 ∧ t.1.val ≤ sk.1.val + 1 ∧
      sk.2.val ≤ t.2.val + 1 ∧ t.2.val ≤ sk.2.val + 1) ∨
      rs.1.val = t.1.val ∨ rs.2.val = t.2.val ∨ BottomFive sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · left; simp only [dInf,absDiff] at king; omega
  by_cases line : RookLine rs t
  · exact Or.inr (by rcases line.2 with x | y; exact Or.inl x; exact Or.inr (Or.inl y))
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have far : 2 ≤ dInf sk t := by omega
  have notCheck : ¬RookSees rs t sk t := fun seen => line seen.1
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone distance notRook far notCheck
  exact Or.inr (Or.inr (Or.inr ((bottom_clear_iff rank low high distinct
    (ne_of_dInf_pos (by omega)) notRook.symm far notCheck).mp (every t step))))

def Region (sk rs wk : Square) : Prop := sk.2.val = 2 ∧
  ((sk.1.val + 1 = wk.1.val ∧ rs.1.val = wk.1.val + 1 ∧ 2 ≤ rs.2.val) ∨
   (sk.1.val = wk.1.val + 1 ∧ rs.1.val + 1 = wk.1.val ∧ 2 ≤ rs.2.val) ∨
   (sk.1.val = wk.1.val ∧ 3 ≤ rs.2.val))

theorem central_six_necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) :
    Terminal sk rs wk ∨ Region sk rs wk := by
  let left : Fin 8 := ⟨wk.1.val - 1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩
  let right : Fin 8 := ⟨wk.1.val + 1,by omega⟩
  have a := covered_box (KRKCastleSix.interior_covered (t := (left,(1 : Fin 8))) safe
    (by simp [dInf,absDiff,left,rank] <;> omega) (by simp [KRKEdgeDepth.depth,left] <;> omega) every)
  have b := covered_box (KRKCastleSix.interior_covered (t := (wk.1,(1 : Fin 8))) safe
    (by simp [dInf,absDiff,rank] <;> omega) (by simp [KRKEdgeDepth.depth] <;> omega) every)
  have c := covered_box (KRKCastleSix.interior_covered (t := (right,(1 : Fin 8))) safe
    (by simp [dInf,absDiff,right,rank] <;> omega) (by simp [KRKEdgeDepth.depth,right] <;> omega) every)
  have l := covered_or_five (t := (left,(0 : Fin 8))) distinct safe
    (by simp [dInf,absDiff,left,rank] <;> omega) rfl (by dsimp [left]; omega) (by dsimp [left]; omega) every
  have r := covered_or_five (t := (right,(0 : Fin 8))) distinct safe
    (by simp [dInf,absDiff,right,rank] <;> omega) rfl (by dsimp [right]; omega) (by dsimp [right]; omega) every
  clear every
  simp [left,right] at a b c
  simp only [SafeRook,dInf,absDiff,rank] at far safe
  simp only [ne_iff_coords] at distinct
  have prison : sk.2.val = 2 ∨ rs.2.val = 1 := by
    clear l r
    omega
  have notOne : rs.2.val ≠ 1 := by
    intro one
    have l0 := l
    have r0 := r
    clear l r
    rw [low_rook_bottom_iff (wk := (left,0)) (by dsimp [left]; omega) (by dsimp [left]; omega) (by omega)] at l0
    rw [low_rook_bottom_iff (wk := (right,0)) (by dsimp [right]; omega) (by dsimp [right]; omega) (by omega)] at r0
    simp [LowRookFive,one,left,right] at l0 r0
    (try simp only [square_eq_iff,Fin.ext_iff] at l0 r0)
    (try dsimp only at l0 r0)
    omega
  have sy : sk.2.val = 2 := prison.resolve_right notOne
  by_cases zero : rs.2.val = 0
  · clear l r
    have center : sk.1.val = wk.1.val := by omega
    have gap : 2 ≤ absDiff rs.1.val wk.1.val := by dsimp [absDiff]; omega
    left
    exact Or.inl ⟨by omega,Or.inl ⟨rank,sy⟩,gap,by omega,by omega,fun _ _ => center⟩
  by_cases two : rs.2.val = 2
  · right
    have l0 := l
    have r0 := r
    clear l r
    rw [rank_two_bottom_iff (wk := (left,0)) (by dsimp [left]; omega) (by dsimp [left]; omega) sy two] at l0
    rw [rank_two_bottom_iff (wk := (right,0)) (by dsimp [right]; omega) (by dsimp [right]; omega) sy two] at r0
    simp [RankTwoFive,sy,two,left,right] at l0 r0
    (try simp only [square_eq_iff,Fin.ext_iff] at l0 r0)
    (try dsimp only at l0 r0)
    dsimp [Region]
    omega
  · clear l r
    right
    have tall : 3 ≤ rs.2.val := by omega
    dsimp [Region]
    omega


/-- Clock-free six-ply forcing adds no central-edge boards to the exact
four-ply region. This does not compress a history-aware rule certificate. -/
theorem kernel_six_four_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4) :
    MateWithin σ 6 q ↔ MateWithin σ 4 q := by
  constructor
  · intro win
    by_cases mate : MatedK q
    · exact Or.inl ⟨turn,mate⟩
    have geometry := (KRKSixGeometry.kernel_six_iff material turn mate).mp win
    have every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u := by
      intro u step; exact geometry.2.2 u (KRKCornerWeakBand.step_guard step)
    rcases central_six_necessary material.1 rank low high far geometry.1 every with terminal | ⟨sy,region⟩
    · exact Or.inl ⟨turn,(KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal⟩
    apply (KRKFourPlyMiddle.weak_four_iff material turn far rank low high).mpr
    rcases region with ⟨sx,rx,ry⟩ | ⟨sx,rx,ry⟩ | ⟨sx,ry⟩
    · exact Or.inr (Or.inl ((KRKThreePly.last_middle_iff rank (by omega) (by omega)).mpr ⟨sy,ry,Or.inr ⟨sx,rx⟩⟩))
    · exact Or.inr (Or.inl ((KRKThreePly.last_middle_iff rank (by omega) (by omega)).mpr ⟨sy,ry,Or.inl ⟨sx,rx⟩⟩))
    · exact Or.inr (Or.inr ⟨sx,sy,ry⟩)
  · intro win; exact mateWithin_mono win (by decide)

end EndgameChess.Rules.KRKSixMiddle
