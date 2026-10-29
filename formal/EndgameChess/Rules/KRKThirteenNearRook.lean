import EndgameChess.Rules.KRKFourteenCentralExact

namespace EndgameChess.Rules.KRKThirteenNearRook
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

inductive Kind where
  | low | side | upperZero | upperOne | upperTwo

def king : Kind → Square
  | .low => (3,1)
  | .side => (3,2)
  | .upperZero => (0,4)
  | .upperOne => (1,4)
  | .upperTwo => (2,4)

def RookRegion (rs : Square) : Kind → Prop
  | .low => rs.2.val = 3 ∧ 3 ≤ rs.1.val
  | .side => (rs.2.val = 3 ∧ 2 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ (rs.2.val = 0 ∨ 4 ≤ rs.2.val))
  | .upperZero => rs.1.val = 2 ∧ 4 ≤ rs.2.val
  | .upperOne => (rs.1.val = 2 ∧ 3 ≤ rs.2.val) ∨ rs = ((3 : Fin 8),2)
  | .upperTwo => rs = ((2 : Fin 8),3) ∨ rs = ((3 : Fin 8),2)

def SideFile (rs : Square) : Prop :=
  (rs.1.val = 1 ∧ (rs.2.val = 1 ∨ 3 ≤ rs.2.val)) ∨
  (rs.2.val = 0 ∧ rs.1.val ≠ 1) ∨ 4 ≤ rs.2.val

def ReachThreeTwo (rs : Square) : Prop :=
  (rs.1.val = 3 ∨ (rs.2.val = 2 ∧ 2 ≤ rs.1.val)) ∧ rs ≠ ((3 : Fin 8),2)

def ReachTwoThree (rs : Square) : Prop :=
  (rs.2.val = 3 ∨ (rs.1.val = 2 ∧ rs.2.val ≤ 2)) ∧ rs ≠ ((2 : Fin 8),3)

def RookCondition (rs : Square) : Kind → Prop
  | .low => KRKNineNearStrip.RookCondition rs
  | .side => KRKElevenNearStrip.SideRow rs ∨ SideFile rs
  | .upperZero => KRKElevenNearStrip.RookCondition rs .upperZero
  | .upperOne => KRKElevenNearStrip.RookCondition rs .upperOne ∨ ReachThreeTwo rs
  | .upperTwo => ReachTwoThree rs ∨ ReachThreeTwo rs

private theorem old_side_subset {rs : Square} (old : KRKElevenNearStrip.RookRegion rs .side) : RookRegion rs .side := by
  rcases old with row | ⟨file,height⟩
  · exact Or.inl row
  · exact Or.inr ⟨file,Or.inr (by omega)⟩

theorem rook_line_necessary {rs nr : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((1 : Fin 8),2)) (sees : RookSees rs nr (king i) (1,2)) (region : RookRegion nr i) :
    RookCondition rs i := by
  cases i with
  | low => exact KRKNineNearStrip.rook_line_necessary apart sees region.1 region.2
  | side =>
    rcases region with row | ⟨file,height⟩
    · have old := KRKElevenNearStrip.rook_line_necessary (i := .side) apart notWeak sees (Or.inl row)
      rcases old with row | file
      · exact Or.inl row
      · apply Or.inr
        dsimp [KRKElevenNearStrip.SideFile] at file
        dsimp [SideFile]
        omega
    · apply Or.inr
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart notWeak
      dsimp [king,SideFile] at sees apart ⊢
      simp_all <;> omega
  | upperZero => exact KRKElevenNearStrip.rook_line_necessary (i := .upperZero) apart notWeak sees region
  | upperOne =>
    rcases region with high | point
    · exact Or.inl (KRKElevenNearStrip.rook_line_necessary (i := .upperOne) apart notWeak sees high)
    · apply Or.inr
      rw [point] at sees
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart notWeak
      dsimp [king,ReachThreeTwo] at sees apart ⊢
      simp only [ne_iff_coords]
      dsimp
      simp_all <;> omega
  | upperTwo =>
    rcases region with point | point
    · apply Or.inl
      rw [point] at sees
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart notWeak
      dsimp [king,ReachTwoThree] at sees apart ⊢
      simp only [ne_iff_coords]
      dsimp
      simp_all <;> omega
    · apply Or.inr
      rw [point] at sees
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart notWeak
      dsimp [king,ReachThreeTwo] at sees apart ⊢
      simp only [ne_iff_coords]
      dsimp
      simp_all <;> omega

private theorem three_two_destination {rs : Square} (condition : ReachThreeTwo rs) :
    RookSees rs ((3 : Fin 8),2) (1,4) (1,2) ∧ RookSees rs ((3 : Fin 8),2) (2,4) (1,2) := by
  dsimp [ReachThreeTwo] at condition
  simp only [ne_iff_coords] at condition
  simp only [RookSees,RookLine,OnSeg,ne_iff_coords]
  dsimp at condition ⊢
  simp_all <;> omega

private theorem two_three_destination {rs : Square} (condition : ReachTwoThree rs) :
    RookSees rs ((2 : Fin 8),3) (2,4) (1,2) := by
  dsimp [ReachTwoThree] at condition
  simp only [ne_iff_coords] at condition
  simp only [RookSees,RookLine,OnSeg,ne_iff_coords]
  dsimp at condition ⊢
  simp_all <;> omega

private theorem side_destination {rs : Square} (condition : RookCondition rs .side) :
    ∃ nr, RookSees rs nr (king .side) (1,2) ∧ RookRegion nr .side := by
  rcases condition with row | file
  · obtain ⟨nr,sees,region⟩ := KRKElevenNearStrip.rook_destination (i := .side) (Or.inl row)
    exact ⟨nr,sees,old_side_subset region⟩
  · rcases file with ⟨rx,one | high⟩ | ⟨zero,notFile⟩ | high
    · refine ⟨((1 : Fin 8),0),?_,Or.inr ⟨rfl,Or.inl rfl⟩⟩
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king,rx,one]
      decide
    · obtain ⟨nr,sees,region⟩ := KRKElevenNearStrip.rook_destination (i := .side) (Or.inr (Or.inl ⟨rx,high⟩))
      exact ⟨nr,sees,old_side_subset region⟩
    · refine ⟨((1 : Fin 8),0),?_,Or.inr ⟨rfl,Or.inl rfl⟩⟩
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king,zero]
      simp_all <;> omega
    · by_cases file : rs.1.val = 1
      · obtain ⟨nr,sees,region⟩ := KRKElevenNearStrip.rook_destination (i := .side) (Or.inr (Or.inl ⟨file,by omega⟩))
        exact ⟨nr,sees,old_side_subset region⟩
      · refine ⟨(1,rs.2),?_,Or.inr ⟨rfl,Or.inr high⟩⟩
        simp only [RookSees,RookLine,OnSeg,ne_iff_coords,king]
        dsimp
        simp_all <;> omega

theorem rook_destination {rs : Square} {i : Kind} (condition : RookCondition rs i) :
    ∃ nr, RookSees rs nr (king i) (1,2) ∧ RookRegion nr i := by
  cases i with
  | low => exact KRKNineNearStrip.rook_destination condition
  | side => exact side_destination condition
  | upperZero => exact KRKElevenNearStrip.rook_destination (i := .upperZero) condition
  | upperOne =>
    rcases condition with high | point
    · obtain ⟨nr,sees,region⟩ := KRKElevenNearStrip.rook_destination (i := .upperOne) high
      exact ⟨nr,sees,Or.inl region⟩
    · exact ⟨(3,2),(three_two_destination point).1,Or.inr rfl⟩
  | upperTwo =>
    rcases condition with point | point
    · exact ⟨(2,3),two_three_destination point,Or.inl rfl⟩
    · exact ⟨(3,2),(three_two_destination point).2,Or.inr rfl⟩

end EndgameChess.Rules.KRKThirteenNearRook
