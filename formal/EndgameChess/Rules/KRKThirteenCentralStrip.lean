import EndgameChess.Rules.KRKFourteenDeepExact

namespace EndgameChess.Rules.KRKThirteenCentralStrip
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem val3 : ((3 : Fin 8).val) = 3 := rfl
private theorem val4 : ((4 : Fin 8).val) = 4 := rfl
private theorem val5 : ((5 : Fin 8).val) = 5 := rfl

inductive Kind where
  | row | opposition | guarded

def king : Kind → Square
  | .row => (3,2)
  | .opposition => (3,3)
  | .guarded => (1,5)

def RookRegion (rs : Square) : Kind → Prop
  | .row => rs.2.val = 4 ∧ 3 ≤ rs.1.val
  | .opposition => rs.1.val = 1 ∧ (rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val)
  | .guarded => rs = ((2 : Fin 8),4)

def RookCondition (rs : Square) : Kind → Prop
  | .row => rs.2.val = 4 ∨ 4 ≤ rs.1.val ∨ (rs.1.val = 3 ∧ 3 ≤ rs.2.val)
  | .opposition => rs.1.val = 1 ∨ rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val
  | .guarded => (rs.1.val = 2 ∨ rs.2.val = 4) ∧ rs ≠ ((2 : Fin 8),4)

theorem region_shape {sk rs : Square} : KRKTwelveCentralExact.Region sk rs ↔
    ∃ i : Kind, sk = king i ∧ RookRegion rs i := by
  constructor
  · rintro (⟨sx,sy,ry,width⟩ | ⟨kingEq,rookEq⟩ | ⟨sx,sy,rx,height⟩)
    · exact ⟨.row,Prod.ext (Fin.ext sx) (Fin.ext sy),ry,width⟩
    · exact ⟨.guarded,kingEq,rookEq⟩
    · exact ⟨.opposition,Prod.ext (Fin.ext sx) (Fin.ext sy),rx,height⟩
  · rintro ⟨i,rfl,region⟩
    cases i with
    | row => exact Or.inl ⟨rfl,rfl,region⟩
    | opposition => exact Or.inr (Or.inr ⟨rfl,rfl,region⟩)
    | guarded => exact Or.inr (Or.inl ⟨rfl,region⟩)

theorem rook_line_necessary {rs nr : Square} {i : Kind}
    (apart : king i ≠ rs) (sees : RookSees rs nr (king i) (1,3)) (region : RookRegion nr i) : RookCondition rs i := by
  cases i with
  | row =>
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart
    dsimp [king,RookRegion,RookCondition] at sees region apart ⊢
    simp_all [val3,val4,val5] <;> omega
  | opposition =>
    have line := sees.1.2
    dsimp [RookRegion,RookCondition] at region ⊢
    (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega
  | guarded =>
    dsimp [RookRegion] at region
    rw [region] at sees
    dsimp [RookCondition]
    exact ⟨sees.1.2,ne_iff_coords.mpr sees.1.1⟩

private theorem row_destination {rs : Square} (condition : RookCondition rs .row) :
    ∃ nr, RookSees rs nr (king .row) (1,3) ∧ RookRegion nr .row := by
  by_cases row : rs.2.val = 4
  · let x : Fin 8 := if rs.1.val = 3 then 4 else 3
    have width : 3 ≤ x.val ∧ x.val ≠ rs.1.val := by dsimp [x]; split <;> (try simp_all) <;> (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega
    refine ⟨(x,4),?_,rfl,width.1⟩
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king,row]
    dsimp; (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega
  · refine ⟨(rs.1,4),?_,rfl,?_⟩
    · dsimp [RookCondition] at condition
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king]
      dsimp; simp_all [val3,val4,val5] <;> omega
    · dsimp [RookCondition] at condition
      change 3 ≤ rs.1.val
      (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega

private theorem opposition_destination {rs : Square} (notWeak : rs ≠ ((1 : Fin 8),3))
    (condition : RookCondition rs .opposition) :
    ∃ nr, RookSees rs nr (king .opposition) (1,3) ∧ RookRegion nr .opposition := by
  by_cases file : rs.1.val = 1
  · let y : Fin 8 := if rs.2.val < 3 then (if rs.2.val = 0 then 1 else 0)
      else (if rs.2.val = 5 then 6 else 5)
    have facts : (y.val ≤ 1 ∨ 5 ≤ y.val) ∧ y.val ≠ rs.2.val ∧
        ¬(rs.2.val < 3 ∧ 3 < y.val ∨ y.val < 3 ∧ 3 < rs.2.val) := by
      simp only [ne_iff_coords] at notWeak
      dsimp [y]
      split <;> split <;> (try simp_all) <;> (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega
    refine ⟨(1,y),?_,rfl,facts.1⟩
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king,file]
    dsimp
    (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega
  · have heights : rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val := by dsimp [RookCondition] at condition; (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega
    refine ⟨(1,rs.2),?_,rfl,heights⟩
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king]
    dsimp
    simp_all [val3,val4,val5] <;> omega

theorem rook_destination {rs : Square} {i : Kind} (notWeak : rs ≠ ((1 : Fin 8),3))
    (condition : RookCondition rs i) : ∃ nr, RookSees rs nr (king i) (1,3) ∧ RookRegion nr i := by
  cases i with
  | row => exact row_destination condition
  | opposition => exact opposition_destination notWeak condition
  | guarded =>
    refine ⟨((2 : Fin 8),4),?_,rfl⟩
    dsimp [RookCondition] at condition
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king]
    simp only [ne_iff_coords] at condition
    dsimp at condition ⊢
    simp_all [val3,val4,val5] <;> omega

def KingEntries (sk rs : Square) : Prop :=
  ∃ i : Kind, dInf sk (king i) = 1 ∧ king i ≠ rs ∧ RookRegion rs i

def RookEntries (sk rs : Square) : Prop := ∃ i : Kind, sk = king i ∧ RookCondition rs i

def Thirteen (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

private theorem far (i : Kind) : 2 ≤ dInf (king i) ((1 : Fin 8),3) := by cases i <;> decide

private theorem region_not_king {rs : Square} {i : Kind} (region : RookRegion rs i) : rs ≠ king i := by
  cases i <;> dsimp [RookRegion,king] at region ⊢ <;>
    simp only [ne_iff_coords,square_eq_iff,Fin.ext_iff] at * <;> (try dsimp) <;> (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega

private theorem region_not_weak {rs : Square} {i : Kind} (region : RookRegion rs i) : rs ≠ ((1 : Fin 8),3) := by
  cases i <;> dsimp [RookRegion] at region <;>
    simp only [ne_iff_coords,square_eq_iff,Fin.ext_iff] at region ⊢ <;> (try dsimp at region ⊢) <;> (try simp_all only [val3,val4,val5,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]) <;> omega

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),3)) :
    KRKThirteenGeometry.Clear sk rs (1,3) ↔ Thirteen sk rs := by
  constructor
  · rintro (immediate | ⟨i,distance,notRook,postFar,region⟩ | ⟨i,equal,a,v,sees,notKing,notRook,region⟩)
    · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
      change 1 = 0 at zero
      contradiction
    · change dInf sk (KRKThirteenSlots.point i) = 1 at distance
      change KRKThirteenSlots.point i ≠ rs at notRook
      change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,3) at region
      obtain ⟨j,kingEq,shape⟩ := region_shape.mp (KRKThirteenInteriorBarriers.central_region_iff.mp region)
      rw [kingEq] at distance notRook
      exact Or.inl ⟨j,distance,notRook,shape⟩
    · let nr := a.target rs v
      change RookSees rs nr sk (1,3) at sees
      change KRKTwelveGlobal.Region sk nr (1,3) at region
      obtain ⟨j,kingEq,shape⟩ := region_shape.mp (KRKThirteenInteriorBarriers.central_region_iff.mp region)
      rw [kingEq] at sees
      exact Or.inr ⟨j,kingEq,rook_line_necessary (by rw [←kingEq]; exact apart) sees shape⟩
  · rintro (⟨i,distance,notRook,region⟩ | ⟨i,equal,condition⟩)
    · exact KRKThirteenGeometry.king_step_clear distance notRook (far i)
        (KRKThirteenInteriorBarriers.central_region_iff.mpr (region_shape.mpr ⟨i,rfl,region⟩))
    · rw [equal] at apart ⊢
      obtain ⟨nr,sees,region⟩ := rook_destination notWeak condition
      exact KRKThirteenGeometry.rook_step_clear sees (region_not_king region) (region_not_weak region)
        (KRKThirteenInteriorBarriers.central_region_iff.mpr (region_shape.mpr ⟨i,rfl,region⟩))

theorem kernel_thirteen_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,3))
    (notCheck : ¬RookSees rs (1,3) sk (1,3)) : MateWithin σ 13 q ↔ Thirteen sk rs :=
  (KRKThirteenGeometry.kernel_thirteen_iff material turn far notCheck).trans (clear_iff material.1 material.2.2.1)

end EndgameChess.Rules.KRKThirteenCentralStrip
