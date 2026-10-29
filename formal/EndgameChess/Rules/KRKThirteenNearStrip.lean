import EndgameChess.Rules.KRKThirteenNearRook

namespace EndgameChess.Rules.KRKThirteenNearStrip
open EndgameChess.KK KRKNativeFrame
open KRKThirteenNearRook (Kind king RookRegion RookCondition rook_line_necessary rook_destination)
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem region_shape {sk rs : Square} : KRKTwelveNearExact.Region sk rs ↔
    ∃ i : Kind, sk = king i ∧ RookRegion rs i := by
  constructor
  · rintro (⟨_,_,sx,sy,ry,width⟩ | ⟨sx,sy,ry,width⟩ | ⟨sx,sy,rx,height⟩ | ⟨sy,rx,zero | one | two⟩ | ⟨sy,xs,rx,ry⟩)
    · exact ⟨.low,Prod.ext (Fin.ext sx) (Fin.ext sy),ry,width⟩
    · exact ⟨.side,Prod.ext (Fin.ext sx) (Fin.ext sy),Or.inl ⟨ry,width⟩⟩
    · exact ⟨.side,Prod.ext (Fin.ext sx) (Fin.ext sy),Or.inr ⟨rx,height⟩⟩
    · exact ⟨.upperZero,Prod.ext (Fin.ext zero.1) (Fin.ext sy),rx,zero.2⟩
    · exact ⟨.upperOne,Prod.ext (Fin.ext one.1) (Fin.ext sy),Or.inl ⟨rx,one.2⟩⟩
    · exact ⟨.upperTwo,Prod.ext (Fin.ext two.1) (Fin.ext sy),Or.inl (Prod.ext (Fin.ext rx) (Fin.ext two.2))⟩
    · have rookEq : rs = ((3 : Fin 8),2) := Prod.ext (Fin.ext rx) (Fin.ext ry)
      rcases xs with one | two
      · exact ⟨.upperOne,Prod.ext (Fin.ext one) (Fin.ext sy),Or.inr rookEq⟩
      · exact ⟨.upperTwo,Prod.ext (Fin.ext two) (Fin.ext sy),Or.inr rookEq⟩
  · rintro ⟨i,rfl,region⟩
    cases i with
    | low => exact Or.inl ⟨rfl,rfl,rfl,rfl,region⟩
    | side =>
      rcases region with row | file
      · exact Or.inr (Or.inl ⟨rfl,rfl,row⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,file⟩))
    | upperZero => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,region.1,Or.inl ⟨rfl,region.2⟩⟩)))
    | upperOne =>
      rcases region with high | point
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,high.1,Or.inr (Or.inl ⟨rfl,high.2⟩)⟩)))
      · rw [point]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,Or.inl rfl,rfl,rfl⟩)))
    | upperTwo =>
      rcases region with point | point
      · rw [point]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩)))
      · rw [point]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,Or.inr rfl,rfl,rfl⟩)))

def KingEntries (sk rs : Square) : Prop :=
  ∃ i : Kind, dInf sk (king i) = 1 ∧ king i ≠ rs ∧ RookRegion rs i

def RookEntries (sk rs : Square) : Prop := ∃ i : Kind, sk = king i ∧ RookCondition rs i

def Thirteen (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

private theorem far (i : Kind) : 2 ≤ dInf (king i) ((1 : Fin 8),2) := by cases i <;> decide

private theorem region_not_king {rs : Square} {i : Kind} (region : RookRegion rs i) : rs ≠ king i := by
  cases i <;> dsimp [RookRegion,king] at region ⊢ <;>
    simp only [ne_iff_coords,square_eq_iff,Fin.ext_iff] at * <;> (try dsimp at region ⊢) <;>
    (try simp_all) <;> omega

private theorem region_not_weak {rs : Square} {i : Kind} (region : RookRegion rs i) : rs ≠ ((1 : Fin 8),2) := by
  cases i <;> dsimp [RookRegion] at region <;>
    simp only [ne_iff_coords,square_eq_iff,Fin.ext_iff] at region ⊢ <;> (try dsimp at region ⊢) <;>
    (try simp_all) <;> omega

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),2)) :
    KRKThirteenGeometry.Clear sk rs (1,2) ↔ Thirteen sk rs := by
  constructor
  · rintro (immediate | ⟨i,distance,notRook,postFar,region⟩ | ⟨i,equal,a,v,sees,notKing,notRook,region⟩)
    · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
      change 1 = 0 at zero
      contradiction
    · change dInf sk (KRKThirteenSlots.point i) = 1 at distance
      change KRKThirteenSlots.point i ≠ rs at notRook
      change KRKTwelveGlobal.Region (KRKThirteenSlots.point i) rs (1,2) at region
      obtain ⟨j,kingEq,shape⟩ := region_shape.mp (KRKThirteenInteriorBarriers.near_region_iff.mp region)
      rw [kingEq] at distance notRook
      exact Or.inl ⟨j,distance,notRook,shape⟩
    · let nr := a.target rs v
      change RookSees rs nr sk (1,2) at sees
      change KRKTwelveGlobal.Region sk nr (1,2) at region
      obtain ⟨j,kingEq,shape⟩ := region_shape.mp (KRKThirteenInteriorBarriers.near_region_iff.mp region)
      rw [kingEq] at sees
      exact Or.inr ⟨j,kingEq,rook_line_necessary (by rw [←kingEq]; exact apart) notWeak sees shape⟩
  · rintro (⟨i,distance,notRook,region⟩ | ⟨i,equal,condition⟩)
    · exact KRKThirteenGeometry.king_step_clear distance notRook (far i)
        (KRKThirteenInteriorBarriers.near_region_iff.mpr (region_shape.mpr ⟨i,rfl,region⟩))
    · rw [equal] at apart ⊢
      obtain ⟨nr,sees,region⟩ := rook_destination condition
      exact KRKThirteenGeometry.rook_step_clear sees (region_not_king region) (region_not_weak region)
        (KRKThirteenInteriorBarriers.near_region_iff.mpr (region_shape.mpr ⟨i,rfl,region⟩))

theorem kernel_thirteen_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,2))
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) : MateWithin σ 13 q ↔ Thirteen sk rs :=
  (KRKThirteenGeometry.kernel_thirteen_iff material turn far notCheck).trans (clear_iff material.1 material.2.2.1)

theorem kernel_exact_thirteen {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,2))
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) :
    (MateWithin σ 13 q ∧ ¬MateWithin σ 12 q) ↔ Thirteen sk rs ∧ ¬KRKElevenNearStrip.Eleven sk rs := by
  constructor
  · rintro ⟨thirteen,notTwelve⟩
    exact ⟨(kernel_thirteen_iff material turn far notCheck).mp thirteen,fun old =>
      notTwelve (mateWithin_mono ((KRKElevenNearStrip.kernel_eleven_iff material turn far notCheck).mpr old) (by decide))⟩
  · rintro ⟨region,notOld⟩
    exact ⟨(kernel_thirteen_iff material turn far notCheck).mpr region,fun twelve =>
      notOld ((KRKElevenNearStrip.kernel_eleven_iff material turn far notCheck).mp
        (KRKTwelveGeometry.strong_twelve_eleven material turn twelve))⟩

end EndgameChess.Rules.KRKThirteenNearStrip
