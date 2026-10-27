import EndgameChess.Rules.KRKFiveMiddle

namespace EndgameChess.Rules.KRKFiveNear
open EndgameChess.KK KRKNativeFrame KRKFiveGeometry
open KRKFourSlots (Kind Valid king Region)
set_option maxHeartbeats 500000

theorem near_slot_properties {wk rs : Square} {i : Kind}
    (rank : wk.2.val = 0) (file : wk.1.val = 1) (valid : Valid wk i) (region : Region wk rs i) :
    king wk i ≠ rs ∧ 2 ≤ dInf (king wk i) wk ∧ Live (king wk i) rs wk ∧ SafeRook (king wk i) rs wk := by
  have near : i = .nearWest ∨ i = .nearMiddle ∨ i = .nearEast := by
    cases i <;> dsimp [Valid] at valid <;> simp <;> omega
  rcases near with rfl | rfl | rfl
  · have step := KRKCanonicalSlots.reply_step (i := .nearWest) (show KRKCanonicalSlots.Valid wk .nearWest from ⟨rank,file⟩) region
    refine ⟨?_,?_,⟨_,KRKCornerWeakBand.step_guard step⟩,?_⟩
    · simp only [ne_iff_coords,king,Region] at region ⊢; (try dsimp only); omega
    · simp only [king,dInf,absDiff,rank]; omega
    · exact Or.inl (by simp only [Region] at region; simp only [dInf,absDiff,rank]; omega)
  · have live : Live (king wk .nearMiddle) rs wk := by
      by_cases rookLeft : rs.1.val = 0
      · refine ⟨(2,0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,king]
        simp only [dInf,absDiff,rank,file,ne_iff_coords,RookSees,RookLine,OnSeg]
        dsimp [Region] at region
        omega
      · refine ⟨(0,0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,king]
        simp only [dInf,absDiff,rank,file,ne_iff_coords,RookSees,RookLine,OnSeg]
        dsimp [Region] at region
        omega
    refine ⟨?_,?_,live,?_⟩
    · simp only [ne_iff_coords,king,Region] at region ⊢; (try dsimp only); omega
    · simp only [king,dInf,absDiff,rank]; omega
    · simp only [SafeRook,king,dInf,absDiff,rank,file,Region] at region ⊢; (try dsimp only); omega
  · have live : Live (king wk .nearEast) rs wk := by
      rcases region with ⟨rx,ry⟩ | ⟨rx,exception⟩
      · refine ⟨(2,0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,king]
        simp only [dInf,absDiff,rank,file,ne_iff_coords,RookSees,RookLine,OnSeg]
        omega
      · by_cases zero : rs.2.val = 0
        · refine ⟨(0,1),?_⟩
          dsimp [KRKCornerWeakBand.Guard,king]
          simp only [dInf,absDiff,rank,file,ne_iff_coords,RookSees,RookLine,OnSeg]
          omega
        · refine ⟨(0,0),?_⟩
          dsimp [KRKCornerWeakBand.Guard,king]
          simp only [dInf,absDiff,rank,file,ne_iff_coords,RookSees,RookLine,OnSeg]
          omega
    refine ⟨?_,?_,live,?_⟩
    · simp only [ne_iff_coords,king,Region] at region ⊢; (try dsimp only); omega
    · simp only [king,dInf,absDiff,rank]; omega
    · simp only [SafeRook,king,dInf,absDiff,rank,file,Region] at region ⊢; (try dsimp only); omega

def KingEntries (sk rs : Square) : Prop :=
  (rs.1.val = 2 ∧ 2 ≤ rs.2.val ∧ dInf sk (0,2) = 1) ∨
  ((3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨ (rs.2.val = 1 ∧ (rs.1.val = 2 ∨ rs.1.val = 3))) ∧ dInf sk (1,2) = 1) ∨
  (((rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨ (3 ≤ rs.1.val ∧ ¬(rs.1.val = 3 ∧ rs.2.val = 1))) ∧ dInf sk (2,2) = 1)

theorem king_points_iff {sk rs wk : Square} (rank : wk.2.val = 0) (file : wk.1.val = 1) :
    KingPoints sk rs wk ↔ KingEntries sk rs := by
  simp only [KingPoints,KRKFiveMiddle.normalize_f rank (by omega),KRKFiveMiddle.normalize_r rank (by omega)]
  constructor
  · rintro ⟨i,valid,region,distance,_⟩
    have near : i = .nearWest ∨ i = .nearMiddle ∨ i = .nearEast := by
      cases i <;> dsimp [Valid] at valid <;> simp <;> omega
    rcases near with rfl | rfl | rfl
    · exact Or.inl ⟨region.1,region.2,distance⟩
    · exact Or.inr (Or.inl ⟨region,distance⟩)
    · exact Or.inr (Or.inr ⟨region,distance⟩)
  · have build : ∀ i, Valid wk i → Region wk rs i → dInf sk (king wk i) = 1 →
        ∃ i, Valid wk i ∧ Region wk rs i ∧ dInf sk (king wk i) = 1 ∧ king wk i ≠ rs ∧
          2 ≤ dInf (king wk i) wk ∧ Live (king wk i) rs wk ∧ SafeRook (king wk i) rs wk := by
      intro i valid region distance
      exact ⟨i,valid,region,distance,near_slot_properties rank file valid region⟩
    rintro (⟨rx,ry,distance⟩ | ⟨region,distance⟩ | ⟨region,distance⟩)
    · exact build .nearWest file ⟨rx,ry⟩ distance
    · exact build .nearMiddle file region distance
    · exact build .nearEast file region distance


theorem west_reachable_iff {sk rs wk : Square} (rank : wk.2.val = 0) (file : wk.1.val = 1)
    (equal : sk = ((0 : Fin 8),2)) (apart : sk ≠ rs) :
    KRKFiveMiddle.Reach sk rs wk .nearWest ↔ rs.1.val = 2 ∨ 2 ≤ rs.2.val := by
  constructor
  · rintro ⟨a,v,sees,region⟩
    rw [equal,ne_iff_coords] at apart
    rw [equal] at sees
    cases a <;> dsimp [KRKCornerSlotBarriers.Axis.target,Region,RookSees,RookLine,OnSeg] at region sees apart ⊢ <;> omega
  · intro condition
    rw [equal,ne_iff_coords] at apart
    by_cases rx : rs.1.val = 2
    · let v : Fin 8 := if rs.2.val = 2 then 3 else 2
      have height : 2 ≤ v.val ∧ v.val ≠ rs.2.val := by dsimp [v]; split <;> simp_all <;> omega
      refine ⟨.file,v,?_,rx,height.1⟩
      rw [equal]
      dsimp [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg,v] at apart height ⊢
      omega
    · have ry : 2 ≤ rs.2.val := condition.resolve_left rx
      refine ⟨.rank,2,?_,rfl,ry⟩
      rw [equal]
      dsimp [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg] at apart ⊢
      omega

theorem middle_reachable {sk rs wk : Square} (rank : wk.2.val = 0) (file : wk.1.val = 1)
    (equal : sk = ((1 : Fin 8),2)) (apartWeak : rs ≠ wk) (notCheck : ¬RookSees rs wk sk wk) :
    KRKFiveMiddle.Reach sk rs wk .nearMiddle := by
  have center : sk = (wk.1,2) := by rw [equal]; exact Prod.ext (Fin.ext file).symm rfl
  obtain ⟨a,v,sees,height⟩ := KRKFiveMiddle.middle_reachable rank center apartWeak notCheck
  exact ⟨a,v,sees,Or.inl height⟩

theorem east_reachable {sk rs wk : Square} (rank : wk.2.val = 0) (file : wk.1.val = 1)
    (equal : sk = ((2 : Fin 8),2)) (apart : sk ≠ rs) (apartWeak : rs ≠ wk) :
    KRKFiveMiddle.Reach sk rs wk .nearEast := by
  rw [equal,ne_iff_coords] at apart
  rw [ne_iff_coords] at apartWeak
  by_cases zero : rs.1.val = 0
  · let v : Fin 8 := if rs.2.val = 2 then 3 else 2
    have height : 2 ≤ v.val ∧ v.val ≠ rs.2.val := by dsimp [v]; split <;> simp_all <;> omega
    refine ⟨.file,v,?_,Or.inl ⟨zero,height.1⟩⟩
    rw [equal]
    dsimp [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg,v] at height ⊢
    omega
  by_cases special : rs.1.val = 1 ∧ rs.2.val = 2
  · refine ⟨.rank,0,?_,Or.inl ⟨rfl,?_⟩⟩
    · rw [equal]
      dsimp [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg]
      omega
    · change 2 ≤ rs.2.val; omega
  · let v : Fin 8 := if rs.1.val = 4 then 5 else 4
    have target : 4 ≤ v.val ∧ v.val ≠ rs.1.val := by dsimp [v]; split <;> simp_all <;> omega
    refine ⟨.rank,v,?_,Or.inr ⟨by change 3 ≤ v.val; omega,?_⟩⟩
    · rw [equal]
      dsimp [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg,v] at target apart apartWeak ⊢
      omega
    · change ¬(v.val = 3 ∧ rs.2.val = 1)
      omega

def RookEntries (sk rs : Square) : Prop :=
  sk = ((1 : Fin 8),2) ∨ sk = ((2 : Fin 8),2) ∨
    (sk = ((0 : Fin 8),2) ∧ (rs.1.val = 2 ∨ 2 ≤ rs.2.val))

theorem rook_rays_iff {sk rs wk : Square} (rank : wk.2.val = 0) (file : wk.1.val = 1)
    (apart : sk ≠ rs) (apartWeak : rs ≠ wk) (notCheck : ¬RookSees rs wk sk wk) :
    RookRays sk rs wk ↔ RookEntries sk rs := by
  simp only [RookRays,KRKFiveMiddle.normalize_f rank (by omega),KRKFiveMiddle.normalize_r rank (by omega)]
  constructor
  · rintro ⟨i,valid,equal,a,v,sees,_,_,region,_⟩
    have near : i = .nearWest ∨ i = .nearMiddle ∨ i = .nearEast := by
      cases i <;> dsimp [Valid] at valid <;> simp <;> omega
    rcases near with rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨equal,(west_reachable_iff rank file equal apart).mp ⟨a,v,sees,region⟩⟩)
    · exact Or.inl equal
    · exact Or.inr (Or.inl equal)
  · have build : ∀ i, Valid wk i → sk = king wk i → KRKFiveMiddle.Reach sk rs wk i →
        ∃ i, Valid wk i ∧ sk = king wk i ∧ ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
          RookSees rs (a.target rs v) sk wk ∧ a.target rs v ≠ sk ∧ a.target rs v ≠ wk ∧
            Region wk (a.target rs v) i ∧ Live sk (a.target rs v) wk ∧ SafeRook sk (a.target rs v) wk := by
      intro i valid equal reach
      obtain ⟨a,v,sees,region⟩ := reach
      obtain ⟨apart,far,live,safe⟩ := near_slot_properties rank file valid region
      have notWeak : a.target rs v ≠ wk := by
        rw [ne_iff_coords]
        cases i <;> dsimp [Valid,Region] at valid region <;> omega
      rw [←equal] at apart live safe
      exact ⟨i,valid,equal,a,v,sees,apart.symm,notWeak,region,live,safe⟩
    rintro (equal | equal | ⟨equal,condition⟩)
    · exact build .nearMiddle file equal (middle_reachable rank file equal apartWeak notCheck)
    · exact build .nearEast file equal (east_reachable rank file equal apart apartWeak)
    · exact build .nearWest file equal ((west_reachable_iff rank file equal apart).mpr condition)

def Five (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

theorem clear_iff {sk rs wk : Square} (rank : wk.2.val = 0) (file : wk.1.val = 1)
    (apart : sk ≠ rs) (apartWeak : rs ≠ wk) (notCheck : ¬RookSees rs wk sk wk) :
    KRKFiveGeometry.Clear sk rs wk ↔ Five sk rs := by
  have depth : KRKEdgeDepth.depth wk = 0 := by simp only [KRKEdgeDepth.depth,rank]; omega
  simp only [KRKFiveGeometry.Clear,depth,true_and,king_points_iff rank file,
    rook_rays_iff rank file apart apartWeak notCheck,Five]
  constructor
  · rintro (immediate | entries)
    · have center := (KRKThreePly.immediate_near_iff (sk := sk) (rs := rs) file rank).mp immediate
      exact Or.inr (Or.inl (Prod.ext (Fin.ext center.1) (Fin.ext center.2.1)))
    · exact entries
  · intro entries; exact Or.inr entries

theorem kernel_five_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) (rank : wk.2.val = 0) (file : wk.1.val = 1) :
    MateWithin σ 5 q ↔ Five sk rs :=
  (KRKFiveGeometry.kernel_five_iff material turn far notCheck).trans
    (clear_iff rank file material.1 material.2.2.1 notCheck)

end EndgameChess.Rules.KRKFiveNear
