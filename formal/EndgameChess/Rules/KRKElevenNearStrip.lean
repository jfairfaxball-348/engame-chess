import EndgameChess.Rules.KRKElevenNearBoundary

namespace EndgameChess.Rules.KRKElevenNearStrip
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

inductive Kind where
  | low | side | upperZero | upperOne

def king : Kind → Square
  | .low => (3,1)
  | .side => (3,2)
  | .upperZero => (0,4)
  | .upperOne => (1,4)

def RookRegion (rs : Square) : Kind → Prop
  | .low => rs.2.val = 3 ∧ 3 ≤ rs.1.val
  | .side => (rs.2.val = 3 ∧ 2 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ (rs.2.val = 4 ∨ rs.2.val = 5))
  | .upperZero => rs.1.val = 2 ∧ 4 ≤ rs.2.val
  | .upperOne => rs.1.val = 2 ∧ 3 ≤ rs.2.val

def SideRow (rs : Square) : Prop :=
  rs.2.val = 3 ∨ rs.1.val = 2 ∨ 4 ≤ rs.1.val ∨ (rs.1.val = 3 ∧ 3 ≤ rs.2.val)

def SideFile (rs : Square) : Prop :=
  (rs.1.val = 1 ∧ 3 ≤ rs.2.val) ∨ rs.2.val = 4 ∨ rs.2.val = 5

def RookCondition (rs : Square) : Kind → Prop
  | .low => KRKNineNearStrip.RookCondition rs
  | .side => SideRow rs ∨ SideFile rs
  | .upperZero => rs.1.val = 2 ∨ 4 ≤ rs.2.val
  | .upperOne => rs.1.val = 2 ∨ (3 ≤ rs.2.val ∧ (rs.2.val ≠ 4 ∨ 2 ≤ rs.1.val))

theorem region_shape {sk rs : Square} : KRKTenNearStrip.Region sk rs ↔
    ∃ i : Kind, sk = king i ∧ RookRegion rs i := by
  constructor
  · intro region
    dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
      KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper] at region
    have cases : (sk = ((3 : Fin 8),1) ∧ rs.2.val = 3 ∧ 3 ≤ rs.1.val) ∨
        (sk = ((3 : Fin 8),2) ∧ ((rs.2.val = 3 ∧ 2 ≤ rs.1.val) ∨
          (rs.1.val = 1 ∧ (rs.2.val = 4 ∨ rs.2.val = 5)))) ∨
        (sk = ((0 : Fin 8),4) ∧ rs.1.val = 2 ∧ 4 ≤ rs.2.val) ∨
        (sk = ((1 : Fin 8),4) ∧ rs.1.val = 2 ∧ 3 ≤ rs.2.val) := by
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp
      omega
    rcases cases with ⟨equal,shape⟩ | ⟨equal,shape⟩ | ⟨equal,shape⟩ | ⟨equal,shape⟩
    · exact ⟨.low,equal,shape⟩
    · exact ⟨.side,equal,shape⟩
    · exact ⟨.upperZero,equal,shape⟩
    · exact ⟨.upperOne,equal,shape⟩
  · rintro ⟨i,rfl,shape⟩
    cases i <;> dsimp [king,RookRegion] at shape ⊢ <;>
      dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
        KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper] <;> omega

theorem global_region_iff {sk rs : Square} : KRKTenGlobal.Region sk rs (1,2) ↔ KRKTenNearStrip.Region sk rs := by
  simp [KRKTenGlobal.Region,KRKTenInteriorExact.Region,KRKEightInteriorExact.stripFrame,
    KRKEdgeDepth.depth,Frame.ofSym,symId]

theorem rook_line_necessary {rs nr : Square} {i : Kind}
    (apart : king i ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),2)) (sees : RookSees rs nr (king i) (1,2)) (region : RookRegion nr i) : RookCondition rs i := by
  cases i with
  | low => exact KRKNineNearStrip.rook_line_necessary apart sees region.1 region.2
  | side =>
    rcases region with row | ⟨file,height⟩
    all_goals
      have line := sees.1.2
      rcases line with vertical | horizontal
    all_goals
      dsimp [RookCondition,SideRow,SideFile] at *
      simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart notWeak
      dsimp at sees apart notWeak
      omega
  | upperZero =>
    have line := sees.1.2
    dsimp [RookCondition,RookRegion] at *
    omega
  | upperOne =>
    have line := sees.1.2
    rcases line with vertical | horizontal
    all_goals
      dsimp [RookCondition,RookRegion] at *
      simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart notWeak
      dsimp at sees apart notWeak
      omega

private theorem side_row_destination {rs : Square} (condition : SideRow rs) :
    ∃ nr, RookSees rs nr (3,2) (1,2) ∧ nr.2.val = 3 ∧ 2 ≤ nr.1.val := by
  by_cases row : rs.2.val = 3
  · let x : Fin 8 := if rs.1.val = 2 then 4 else 2
    have width : 2 ≤ x.val ∧ x.val ≠ rs.1.val := by dsimp [x]; split <;> (try simp_all) <;> omega
    refine ⟨(x,3),?_,rfl,width.1⟩
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  · refine ⟨(rs.1,3),?_,rfl,?_⟩
    · dsimp [SideRow] at condition
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords]
      simp <;> omega
    · dsimp [SideRow] at condition
      change 2 ≤ rs.1.val
      omega

private theorem side_file_destination {rs : Square} (condition : SideFile rs) :
    ∃ nr, RookSees rs nr (3,2) (1,2) ∧ nr.1.val = 1 ∧ (nr.2.val = 4 ∨ nr.2.val = 5) := by
  by_cases file : rs.1.val = 1
  · let y : Fin 8 := if rs.2.val = 4 then 5 else 4
    have height : (y.val = 4 ∨ y.val = 5) ∧ y.val ≠ rs.2.val := by dsimp [y]; split <;> (try simp_all) <;> omega
    refine ⟨(1,y),?_,rfl,height.1⟩
    dsimp [SideFile] at condition
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,file]
    simp <;> omega
  · refine ⟨(1,rs.2),?_,rfl,?_⟩
    · dsimp [SideFile] at condition
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords]
      simp <;> omega
    · dsimp [SideFile] at condition
      change rs.2.val = 4 ∨ rs.2.val = 5
      omega

theorem rook_destination {rs : Square} {i : Kind} (condition : RookCondition rs i) :
    ∃ nr, RookSees rs nr (king i) (1,2) ∧ RookRegion nr i := by
  cases i with
  | low => exact KRKNineNearStrip.rook_destination condition
  | side =>
    rcases condition with row | file
    · obtain ⟨nr,sees,shape⟩ := side_row_destination row
      exact ⟨nr,sees,Or.inl shape⟩
    · obtain ⟨nr,sees,shape⟩ := side_file_destination file
      exact ⟨nr,sees,Or.inr shape⟩
  | upperZero =>
    by_cases file : rs.1.val = 2
    · let y : Fin 8 := if rs.2.val = 4 then 5 else 4
      have height : 4 ≤ y.val ∧ y.val ≠ rs.2.val := by dsimp [y]; split <;> (try simp_all) <;> omega
      refine ⟨(2,y),?_,rfl,height.1⟩
      simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords,file]
      simp <;> omega
    · refine ⟨(2,rs.2),?_,rfl,?_⟩
      · dsimp [RookCondition] at condition
        simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords]
        simp <;> omega
      · change 4 ≤ rs.2.val
        dsimp [RookCondition] at condition
        omega
  | upperOne =>
    by_cases file : rs.1.val = 2
    · let y : Fin 8 := if rs.2.val = 4 then 5 else 4
      have height : 3 ≤ y.val ∧ y.val ≠ rs.2.val := by dsimp [y]; split <;> (try simp_all) <;> omega
      refine ⟨(2,y),?_,rfl,height.1⟩
      simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords,file]
      simp <;> omega
    · refine ⟨(2,rs.2),?_,rfl,?_⟩
      · dsimp [RookCondition] at condition
        simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords]
        simp <;> omega
      · change 3 ≤ rs.2.val
        dsimp [RookCondition] at condition
        omega

def KingEntries (sk rs : Square) : Prop :=
  ∃ i : Kind, dInf sk (king i) = 1 ∧ king i ≠ rs ∧ RookRegion rs i

def RookEntries (sk rs : Square) : Prop :=
  ∃ i : Kind, sk = king i ∧ RookCondition rs i

def Eleven (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

private theorem frame_f (s : Square) : (KRKElevenSlots.frame ((1 : Fin 8),2)).f s = s := rfl
private theorem frame_r (s : Square) : (KRKElevenSlots.frame ((1 : Fin 8),2)).r s = s := rfl

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (sourceNotWeak : rs ≠ ((1 : Fin 8),2)) :
    KRKElevenGeometry.Clear sk rs (1,2) ↔ Eleven sk rs := by
  constructor
  · rintro (immediate | points | rays)
    · dsimp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,
        KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
      omega
    · obtain ⟨j,distance,notRook,far,region⟩ := points
      simp only [frame_f,frame_r] at distance notRook region
      obtain ⟨i,equal,shape⟩ := region_shape.mp (global_region_iff.mp region)
      rw [equal] at distance notRook
      exact Or.inl ⟨i,distance,notRook,shape⟩
    · obtain ⟨j,equal,a,v,sees,notKing,notWeak,region⟩ := rays
      simp only [frame_f,frame_r] at equal sees notKing notWeak region
      obtain ⟨i,kingEq,shape⟩ := region_shape.mp (global_region_iff.mp region)
      rw [kingEq] at sees apart
      exact Or.inr ⟨i,kingEq,rook_line_necessary apart sourceNotWeak sees shape⟩
  · rintro (⟨i,distance,notRook,shape⟩ | ⟨i,rfl,condition⟩)
    · have region := global_region_iff.mpr (region_shape.mpr ⟨i,rfl,shape⟩)
      apply KRKElevenGeometry.king_step_clear distance notRook ?_ region
      cases i <;> decide
    · obtain ⟨nr,sees,shape⟩ := rook_destination condition
      have region := global_region_iff.mpr (region_shape.mpr ⟨i,rfl,shape⟩)
      have notKing : nr ≠ king i := by
        cases i <;> dsimp [RookRegion,king] at shape ⊢ <;>
          simp only [ne_iff_coords] <;> dsimp <;> omega
      have notWeak : nr ≠ ((1 : Fin 8),2) := by
        cases i <;> dsimp [RookRegion] at shape <;>
          simp only [ne_iff_coords] <;> dsimp <;> omega
      exact KRKElevenGeometry.rook_step_clear sees notKing notWeak region

theorem kernel_eleven_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,2))
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) : MateWithin σ 11 q ↔ Eleven sk rs :=
  (KRKElevenGeometry.kernel_eleven_iff material turn far notCheck).trans (clear_iff material.1 material.2.2.1)

theorem kernel_exact_eleven {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,2))
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) :
    (MateWithin σ 11 q ∧ ¬MateWithin σ 10 q) ↔
      Eleven sk rs ∧ ¬KRKNineNearStrip.Nine sk rs := by
  constructor
  · rintro ⟨eleven,notTen⟩
    exact ⟨(kernel_eleven_iff material turn far notCheck).mp eleven,fun nine =>
      notTen (mateWithin_mono ((KRKNineNearStrip.kernel_nine_iff material turn far).mpr nine) (by decide))⟩
  · rintro ⟨region,notNine⟩
    exact ⟨(kernel_eleven_iff material turn far notCheck).mpr region,fun ten =>
      notNine ((KRKNineNearStrip.kernel_nine_iff material turn far).mp
        (KRKTenGeometry.strong_ten_nine material turn ten))⟩

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),2))
    (apart : sk ≠ rs) (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) :
    KRKElevenGeometry.Clear sk rs wk ↔ Eleven (g.f sk) (g.f rs) := by
  have notKing : sk ≠ wk := ne_of_dInf_pos (by omega)
  constructor
  · intro clear
    have mapped := KRKElevenGeometry.frame_map g apart notKing notRook far notCheck clear
    rw [target] at mapped
    exact (clear_iff (g.ne_iff.mpr apart) (target ▸ g.ne_iff.mpr notRook)).mp mapped
  · intro region
    have mapped := (clear_iff (g.ne_iff.mpr apart) (target ▸ g.ne_iff.mpr notRook)).mpr region
    have shaped : KRKElevenGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr apart)
      (g.ne_iff.mpr notKing) (g.ne_iff.mpr notRook) (by rw [g.distance]; exact far)
      (fun h => notCheck ((g.sees _ _ _ _).mp h)) shaped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKElevenNearStrip
