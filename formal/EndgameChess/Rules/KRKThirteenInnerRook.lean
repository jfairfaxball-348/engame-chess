import EndgameChess.Rules.KRKThirteenNearStrip

namespace EndgameChess.Rules.KRKThirteenInnerRook
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/- Every rook source has a non-null ray into the high inward region. -/
theorem high_destination (rs : Square) :
    ∃ nr, RookSees rs nr (3,2) (1,1) ∧ nr ≠ ((3 : Fin 8),2) ∧
      nr ≠ ((1 : Fin 8),1) ∧ KRKTwelveInnerHighExact.Region nr := by
  by_cases zero : rs.2.val = 0
  · let x : Fin 8 := if rs.1.val = 4 then 5 else 4
    refine ⟨(x,0),?_,?_,?_,?_⟩
    all_goals simp only [RookSees,RookLine,OnSeg,ne_iff_coords,KRKTwelveInnerHighExact.Region,square_eq_iff,Fin.ext_iff]
    all_goals dsimp [x]
    all_goals (first | split | skip) <;> simp_all <;> omega
  by_cases one : rs.2.val = 1
  · by_cases left : rs.1.val ≤ 1
    · refine ⟨(rs.1,3),?_,?_,?_,?_⟩
      all_goals simp only [RookSees,RookLine,OnSeg,ne_iff_coords,KRKTwelveInnerHighExact.Region,square_eq_iff,Fin.ext_iff]
      all_goals dsimp
      all_goals simp_all <;> omega
    · let x : Fin 8 := if rs.1.val = 4 then 5 else 4
      refine ⟨(x,1),?_,?_,?_,?_⟩
      all_goals simp only [RookSees,RookLine,OnSeg,ne_iff_coords,KRKTwelveInnerHighExact.Region,square_eq_iff,Fin.ext_iff]
      all_goals dsimp [x]
      all_goals (first | split | skip) <;> simp_all <;> omega
  by_cases two : rs.2.val = 2
  · refine ⟨(rs.1,3),?_,?_,?_,?_⟩
    all_goals simp only [RookSees,RookLine,OnSeg,ne_iff_coords,KRKTwelveInnerHighExact.Region,square_eq_iff,Fin.ext_iff]
    all_goals dsimp
    all_goals simp_all <;> omega
  · let x : Fin 8 := if rs.1.val = 2 then 3 else 2
    refine ⟨(x,rs.2),?_,?_,?_,?_⟩
    all_goals simp only [RookSees,RookLine,OnSeg,ne_iff_coords,KRKTwelveInnerHighExact.Region,square_eq_iff,Fin.ext_iff]
    all_goals dsimp [x]
    all_goals (first | split | skip) <;> simp_all <;> omega

inductive Kind where
  | low | side | high | diagonal | outerLow | outerHigh
  | upperZero | upperOne | upperTwo | upperHigh

def king : Kind → Square
  | .low => (3,0)
  | .side => (3,1)
  | .high => (3,2)
  | .diagonal => (3,3)
  | .outerLow => (4,1)
  | .outerHigh => (4,2)
  | .upperZero => (0,4)
  | .upperOne => (1,4)
  | .upperTwo => (2,4)
  | .upperHigh => (1,5)

def RookRegion (rs : Square) : Kind → Prop
  | .low => rs.2.val = 2 ∧ 3 ≤ rs.1.val
  | .side => KRKTwelveInnerSide.Region rs
  | .high => KRKTwelveInnerHighExact.Region rs
  | .diagonal => KRKTwelveInnerDiagonalExact.Region rs
  | .outerLow | .outerHigh => rs = ((2 : Fin 8),3)
  | .upperZero | .upperOne => rs.1.val = 2 ∧ 3 ≤ rs.2.val
  | .upperTwo => rs = ((2 : Fin 8),3)
  | .upperHigh => rs = ((2 : Fin 8),4)

def RookCondition (rs : Square) : Kind → Prop
  | .low => rs.2.val = 2 ∨ 3 ≤ rs.1.val
  | .side | .high => True
  | .diagonal => rs.1.val = 2 ∨ rs.2.val = 2 ∨
      (rs.1.val = 3 ∧ rs.2.val ≤ 1) ∨ (rs.2.val = 3 ∧ rs.1.val ≤ 1)
  | .outerLow | .outerHigh => (rs.1.val = 2 ∨ rs.2.val = 3) ∧ rs ≠ ((2 : Fin 8),3)
  | .upperZero => rs.1.val = 2 ∨ 3 ≤ rs.2.val
  | .upperOne => rs.1.val = 2 ∨ (3 ≤ rs.2.val ∧ (rs.2.val ≠ 4 ∨ 2 ≤ rs.1.val))
  | .upperTwo => KRKThirteenNearRook.ReachTwoThree rs
  | .upperHigh => (rs.1.val = 2 ∨ rs.2.val = 4) ∧ rs ≠ ((2 : Fin 8),4)

theorem rook_line_necessary {rs nr : Square} {i : Kind} (apart : king i ≠ rs)
    (sees : RookSees rs nr (king i) (1,1)) (region : RookRegion nr i) :
    RookCondition rs i := by
  cases i <;> dsimp [king,RookRegion,RookCondition,KRKTwelveInnerDiagonalExact.Region,
    KRKThirteenNearRook.ReachTwoThree] at apart sees region ⊢
  all_goals simp only [RookSees,RookLine,OnSeg,ne_iff_coords,square_eq_iff,Fin.ext_iff] at *
  all_goals (try dsimp at *)
  all_goals (try simp_all)
  all_goals omega

private theorem region_not_king {nr : Square} {i : Kind} (notHigh : i ≠ .high)
    (region : RookRegion nr i) : nr ≠ king i := by
  cases i <;> simp only [RookRegion,king,KRKTwelveInnerSide.Region,
    KRKNineNearStrip.RookCondition,KRKTwelveInnerDiagonalExact.Region,ne_iff_coords,
    square_eq_iff,Fin.ext_iff] at * <;> (try dsimp at *) <;> (try simp_all) <;> omega

private theorem region_not_weak {nr : Square} {i : Kind} (region : RookRegion nr i) :
    nr ≠ ((1 : Fin 8),1) := by
  cases i <;> simp only [RookRegion,KRKTwelveInnerSide.Region,KRKTwelveInnerHighExact.Region,
    KRKNineNearStrip.RookCondition,KRKTwelveInnerDiagonalExact.Region,ne_iff_coords,
    square_eq_iff,Fin.ext_iff] at * <;> (try dsimp at *) <;> (try simp_all) <;> omega

end EndgameChess.Rules.KRKThirteenInnerRook
