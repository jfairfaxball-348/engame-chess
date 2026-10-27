import EndgameChess.Rules.KRKFiveGeometry

namespace EndgameChess.Rules.KRKFiveMiddle
open EndgameChess.KK KRKNativeFrame KRKFiveGeometry
open KRKFourSlots (Kind Valid king Region)
set_option maxHeartbeats 500000

theorem normalize_f {wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) (s : Square) :
    (normalize wk).f s = s := by
  simp [normalize,bottomFrame,rank,high,Frame.ofSym,symId]

theorem normalize_r {wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) (s : Square) :
    (normalize wk).r s = s := by
  simp [normalize,bottomFrame,rank,high,Frame.ofSym,symId]

theorem middle_slot_properties {wk rs : Square} {i : Kind}
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 3)
    (valid : Valid wk i) (region : Region wk rs i) :
    king wk i ≠ rs ∧ 2 ≤ dInf (king wk i) wk ∧ Live (king wk i) rs wk ∧ SafeRook (king wk i) rs wk := by
  have middle : i = .middleWest ∨ i = .middleMiddle ∨ i = .middleEast := by
    cases i <;> dsimp [Valid] at valid <;> simp <;> omega
  rcases middle with rfl | rfl | rfl
  · have step := KRKCanonicalSlots.reply_step (i := .middleWest)
      (show KRKCanonicalSlots.Valid wk .middleWest from ⟨rank,low,high⟩) region
    refine ⟨?_,?_,⟨_,KRKCornerWeakBand.step_guard step⟩,?_⟩
    · simp only [ne_iff_coords,king,Region,KRKCanonicalSlots.left,KRKCanonicalSlots.right] at region ⊢
      omega
    · simp only [king,dInf,absDiff,rank]; omega
    · exact Or.inl (by simp only [Region] at region; simp only [dInf,absDiff,rank]; omega)
  · have ry : 3 ≤ rs.2.val := region
    have live : Live (king wk .middleMiddle) rs wk := by
      by_cases left : rs.1.val = (KRKCanonicalSlots.left wk).val
      · refine ⟨(KRKCanonicalSlots.right wk,0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,king]
        simp only [dInf,absDiff,rank,ne_iff_coords,RookSees,RookLine,OnSeg,KRKCanonicalSlots.right]
        dsimp [KRKCanonicalSlots.left] at left
        omega
      · refine ⟨(KRKCanonicalSlots.left wk,0),?_⟩
        dsimp [KRKCornerWeakBand.Guard,king]
        simp only [dInf,absDiff,rank,ne_iff_coords,RookSees,RookLine,OnSeg,KRKCanonicalSlots.left]
        dsimp [KRKCanonicalSlots.left] at left
        omega
    refine ⟨?_,?_,live,?_⟩
    · simp only [ne_iff_coords,king]; omega
    · simp only [king,dInf,absDiff,rank]; omega
    · exact Or.inl (by simp only [dInf,absDiff,rank]; omega)
  · have step := KRKCanonicalSlots.reply_step (i := .middleEast)
      (show KRKCanonicalSlots.Valid wk .middleEast from ⟨rank,low,high⟩) region
    refine ⟨?_,?_,⟨_,KRKCornerWeakBand.step_guard step⟩,?_⟩
    · simp only [ne_iff_coords,king,Region,KRKCanonicalSlots.left,KRKCanonicalSlots.right] at region ⊢
      omega
    · simp only [king,dInf,absDiff,rank]; omega
    · exact Or.inl (by simp only [Region] at region; simp only [dInf,absDiff,rank]; omega)

def KingEntries (sk rs wk : Square) : Prop :=
  (3 ≤ rs.2.val ∧ dInf sk (wk.1,2) = 1) ∨
  (rs.1.val = (KRKCanonicalSlots.right wk).val ∧ 2 ≤ rs.2.val ∧ dInf sk (KRKCanonicalSlots.left wk,2) = 1) ∨
  (rs.1.val = (KRKCanonicalSlots.left wk).val ∧ 2 ≤ rs.2.val ∧ dInf sk (KRKCanonicalSlots.right wk,2) = 1)

theorem king_points_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 3) : KingPoints sk rs wk ↔ KingEntries sk rs wk := by
  simp only [KingPoints,normalize_f rank high,normalize_r rank high]
  constructor
  · rintro ⟨i,valid,region,distance,_⟩
    have middle : i = .middleWest ∨ i = .middleMiddle ∨ i = .middleEast := by
      cases i <;> dsimp [Valid] at valid <;> simp <;> omega
    rcases middle with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨region.1,region.2,distance⟩)
    · exact Or.inl ⟨region,distance⟩
    · exact Or.inr (Or.inr ⟨region.1,region.2,distance⟩)
  · intro entries
    have build : ∀ i, Valid wk i → Region wk rs i → dInf sk (king wk i) = 1 →
        ∃ i, Valid wk i ∧ Region wk rs i ∧ dInf sk (king wk i) = 1 ∧ king wk i ≠ rs ∧
          2 ≤ dInf (king wk i) wk ∧ Live (king wk i) rs wk ∧ SafeRook (king wk i) rs wk := by
      intro i valid region distance
      exact ⟨i,valid,region,distance,middle_slot_properties rank low high valid region⟩
    rcases entries with ⟨ry,distance⟩ | ⟨rx,ry,distance⟩ | ⟨rx,ry,distance⟩
    · exact build .middleMiddle ⟨low,high⟩ ry distance
    · exact build .middleWest ⟨low,high⟩ ⟨rx,ry⟩ distance
    · exact build .middleEast ⟨low,high⟩ ⟨rx,ry⟩ distance


def Reach (sk rs wk : Square) (i : Kind) : Prop :=
  ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
    RookSees rs (a.target rs v) sk wk ∧ Region wk (a.target rs v) i

theorem middle_reachable {sk rs wk : Square} (rank : wk.2.val = 0)
    (equal : sk = (wk.1,2)) (apartWeak : rs ≠ wk) (notCheck : ¬RookSees rs wk sk wk) :
    Reach sk rs wk .middleMiddle := by
  have fileHigh : rs.1.val = wk.1.val → 3 ≤ rs.2.val := by
    intro file
    by_cases tall : 3 ≤ rs.2.val
    · exact tall
    · apply False.elim
      apply notCheck
      simp only [ne_iff_coords] at apartWeak
      simp only [RookSees,RookLine,OnSeg,equal,rank]
      (try dsimp only)
      omega
  let v : Fin 8 := if rs.2.val = 3 then 4 else 3
  have height : 3 ≤ v.val ∧ v.val ≠ rs.2.val := by dsimp [v]; split <;> simp_all <;> omega
  refine ⟨.file,v,?_,height.1⟩
  dsimp [KRKCornerSlotBarriers.Axis.target,RookSees,RookLine,OnSeg]
  rw [equal]
  dsimp only
  by_cases file : rs.1.val = wk.1.val
  · have tall := fileHigh file
    omega
  · omega

theorem west_reachable_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 3)
    (equal : sk = (KRKCanonicalSlots.left wk,2)) (apart : sk ≠ rs) :
    Reach sk rs wk .middleWest ↔
      rs.1.val = (KRKCanonicalSlots.right wk).val ∨ 3 ≤ rs.2.val ∨
        (rs.2.val = 2 ∧ wk.1.val ≤ rs.1.val) := by
  constructor
  · rintro ⟨a,v,sees,region⟩
    rw [equal,ne_iff_coords] at apart
    rw [equal] at sees
    cases a <;>
      dsimp [KRKCornerSlotBarriers.Axis.target,Region,RookSees,RookLine,OnSeg,
        KRKCanonicalSlots.left,KRKCanonicalSlots.right] at region sees apart ⊢ <;> omega
  · intro condition
    by_cases file : rs.1.val = (KRKCanonicalSlots.right wk).val
    · let v : Fin 8 := if rs.2.val = 2 then 3 else 2
      have height : 2 ≤ v.val ∧ v.val ≠ rs.2.val := by dsimp [v]; split <;> simp_all <;> omega
      refine ⟨.file,v,?_,?_,height.1⟩
      · rw [equal]
        dsimp [RookSees,RookLine,OnSeg,KRKCornerSlotBarriers.Axis.target,v,
          KRKCanonicalSlots.left,KRKCanonicalSlots.right] at file height ⊢
        omega
      · exact file
    · refine ⟨.rank,KRKCanonicalSlots.right wk,?_,rfl,?_⟩
      · rw [equal]
        dsimp [RookSees,RookLine,OnSeg,KRKCornerSlotBarriers.Axis.target,
          KRKCanonicalSlots.left,KRKCanonicalSlots.right] at file condition ⊢
        omega
      · change 2 ≤ rs.2.val
        rcases condition with impossible | tall | ⟨height,_⟩
        · exact False.elim (file impossible)
        · omega
        · omega

theorem east_reachable_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 3)
    (equal : sk = (KRKCanonicalSlots.right wk,2)) (apart : sk ≠ rs) :
    Reach sk rs wk .middleEast ↔
      rs.1.val = (KRKCanonicalSlots.left wk).val ∨ 3 ≤ rs.2.val ∨
        (rs.2.val = 2 ∧ rs.1.val ≤ wk.1.val) := by
  constructor
  · rintro ⟨a,v,sees,region⟩
    rw [equal,ne_iff_coords] at apart
    rw [equal] at sees
    cases a <;>
      dsimp [KRKCornerSlotBarriers.Axis.target,Region,RookSees,RookLine,OnSeg,
        KRKCanonicalSlots.left,KRKCanonicalSlots.right] at region sees apart ⊢ <;> omega
  · intro condition
    by_cases file : rs.1.val = (KRKCanonicalSlots.left wk).val
    · let v : Fin 8 := if rs.2.val = 2 then 3 else 2
      have height : 2 ≤ v.val ∧ v.val ≠ rs.2.val := by dsimp [v]; split <;> simp_all <;> omega
      refine ⟨.file,v,?_,?_,height.1⟩
      · rw [equal]
        dsimp [RookSees,RookLine,OnSeg,KRKCornerSlotBarriers.Axis.target,v,
          KRKCanonicalSlots.left,KRKCanonicalSlots.right] at file height ⊢
        omega
      · exact file
    · refine ⟨.rank,KRKCanonicalSlots.left wk,?_,rfl,?_⟩
      · rw [equal]
        dsimp [RookSees,RookLine,OnSeg,KRKCornerSlotBarriers.Axis.target,
          KRKCanonicalSlots.left,KRKCanonicalSlots.right] at file condition ⊢
        omega
      · change 2 ≤ rs.2.val
        rcases condition with impossible | tall | ⟨height,_⟩
        · exact False.elim (file impossible)
        · omega
        · omega


def RookEntries (sk rs wk : Square) : Prop :=
  sk = (wk.1,2) ∨
    (sk = (KRKCanonicalSlots.left wk,2) ∧
      (rs.1.val = (KRKCanonicalSlots.right wk).val ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ wk.1.val ≤ rs.1.val))) ∨
    (sk = (KRKCanonicalSlots.right wk,2) ∧
      (rs.1.val = (KRKCanonicalSlots.left wk).val ∨ 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ rs.1.val ≤ wk.1.val)))

theorem rook_rays_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 3) (apart : sk ≠ rs) (apartWeak : rs ≠ wk)
    (notCheck : ¬RookSees rs wk sk wk) : RookRays sk rs wk ↔ RookEntries sk rs wk := by
  simp only [RookRays,normalize_f rank high,normalize_r rank high]
  constructor
  · rintro ⟨i,valid,equal,a,v,sees,_,_,region,_⟩
    have middle : i = .middleWest ∨ i = .middleMiddle ∨ i = .middleEast := by
      cases i <;> dsimp [Valid] at valid <;> simp <;> omega
    rcases middle with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨equal,(west_reachable_iff rank low high equal apart).mp ⟨a,v,sees,region⟩⟩)
    · exact Or.inl equal
    · exact Or.inr (Or.inr ⟨equal,(east_reachable_iff rank low high equal apart).mp ⟨a,v,sees,region⟩⟩)
  · have build : ∀ i, Valid wk i → sk = king wk i → Reach sk rs wk i →
        ∃ i, Valid wk i ∧ sk = king wk i ∧ ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
          RookSees rs (a.target rs v) sk wk ∧ a.target rs v ≠ sk ∧ a.target rs v ≠ wk ∧
            Region wk (a.target rs v) i ∧ Live sk (a.target rs v) wk ∧ SafeRook sk (a.target rs v) wk := by
      intro i valid equal reach
      obtain ⟨a,v,sees,region⟩ := reach
      obtain ⟨apart,far,live,safe⟩ := middle_slot_properties rank low high valid region
      have height : 2 ≤ (a.target rs v).2.val := by
        cases i <;> dsimp [Valid,Region] at valid region <;> omega
      have notWeak : a.target rs v ≠ wk := by
        rw [ne_iff_coords]; omega
      rw [←equal] at apart live safe
      exact ⟨i,valid,equal,a,v,sees,apart.symm,notWeak,region,live,safe⟩
    rintro (equal | ⟨equal,condition⟩ | ⟨equal,condition⟩)
    · exact build .middleMiddle ⟨low,high⟩ equal (middle_reachable rank equal apartWeak notCheck)
    · exact build .middleWest ⟨low,high⟩ equal ((west_reachable_iff rank low high equal apart).mpr condition)
    · exact build .middleEast ⟨low,high⟩ equal ((east_reachable_iff rank low high equal apart).mpr condition)

/-- No entry searches remain: three king-distance tests and three explicit
rook-placement alternatives evaluate the canonical middle five-ply geometry. -/
def Five (sk rs wk : Square) : Prop := KingEntries sk rs wk ∨ RookEntries sk rs wk

theorem clear_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 3) (apart : sk ≠ rs) (apartWeak : rs ≠ wk)
    (notCheck : ¬RookSees rs wk sk wk) : KRKFiveGeometry.Clear sk rs wk ↔ Five sk rs wk := by
  have depth : KRKEdgeDepth.depth wk = 0 := by simp only [KRKEdgeDepth.depth,rank]; omega
  simp only [KRKFiveGeometry.Clear,depth,true_and,king_points_iff rank low high,
    rook_rays_iff rank low high apart apartWeak notCheck,Five]
  constructor
  · rintro (immediate | entries)
    · have center := (KRKThreePly.immediate_middle_iff (sk := sk) (rs := rs) rank low (by omega)).mp immediate
      exact Or.inr (Or.inl (Prod.ext (Fin.ext center.1) (Fin.ext center.2.1)))
    · exact entries
  · intro entries; exact Or.inr entries

theorem kernel_five_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 3) : MateWithin σ 5 q ↔ Five sk rs wk :=
  (KRKFiveGeometry.kernel_five_iff material turn far notCheck).trans
    (clear_iff rank low high material.1 material.2.2.1 notCheck)


def BottomFive (sk rs wk : Square) : Prop :=
  if wk.1.val ≤ 3 then Five sk rs wk else Five (symX.f sk) (symX.f rs) (symX.f wk)

theorem bottom_clear_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) (apart : sk ≠ rs) (apartKing : sk ≠ wk)
    (apartWeak : rs ≠ wk) (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) :
    KRKFiveGeometry.Clear sk rs wk ↔ BottomFive sk rs wk := by
  by_cases small : wk.1.val ≤ 3
  · simp only [BottomFive,small,↓reduceIte]
    exact clear_iff rank low small apart apartWeak notCheck
  · simp only [BottomFive,small,↓reduceIte]
    have flipped := clear_iff (sk := symX.f sk) (rs := symX.f rs) (wk := symX.f wk)
      rank (by dsimp [symX]; omega) (by dsimp [symX]; omega)
      (symX.ne_iff.mpr apart) (symX.ne_iff.mpr apartWeak)
      (fun seen => notCheck ((symX.sees_iff _ _ _ _).mp seen))
    exact (KRKFiveGeometry.map_iff symX apart apartKing apartWeak far notCheck).symm.trans flipped


def LowRookFive (sk rs wk : Square) : Prop := sk.2.val = 2 ∧
  (sk.1.val = wk.1.val ∨ (sk.1.val + 1 = wk.1.val ∧ rs.1.val = wk.1.val + 1) ∨
    (sk.1.val = wk.1.val + 1 ∧ rs.1.val + 1 = wk.1.val))

theorem low_rook_bottom_iff {sk rs wk : Square}
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) (height : rs.2.val ≤ 1) :
    BottomFive sk rs wk ↔ LowRookFive sk rs wk := by
  have notTwo : ¬2 ≤ rs.2.val := by omega
  have notThree : ¬3 ≤ rs.2.val := by omega
  have notEq : rs.2.val ≠ 2 := by omega
  unfold BottomFive
  split <;>
    simp only [Five,KingEntries,RookEntries] <;>
    (try dsimp only [symX]) <;>
    simp only [notTwo,notThree,notEq,false_and,and_false,false_or,or_false] <;>
    simp only [square_eq_iff,Fin.ext_iff] <;>
    dsimp [LowRookFive,KRKCanonicalSlots.left,KRKCanonicalSlots.right] <;> constructor <;> intro h <;> omega


def RankTwoFive (sk rs wk : Square) : Prop :=
  sk.1.val = wk.1.val ∨
  (sk.1.val + 1 = wk.1.val ∧ (rs.1.val = wk.1.val + 1 ∨ wk.1.val ≤ rs.1.val)) ∨
  (sk.1.val = wk.1.val + 1 ∧ (rs.1.val + 1 = wk.1.val ∨ rs.1.val ≤ wk.1.val)) ∨
  (sk.1.val + 2 = wk.1.val ∧ rs.1.val = wk.1.val + 1) ∨
  (sk.1.val = wk.1.val + 2 ∧ rs.1.val + 1 = wk.1.val)

theorem rank_two_bottom_iff {sk rs wk : Square}
    (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5) (sy : sk.2.val = 2) (ry : rs.2.val = 2) :
    BottomFive sk rs wk ↔ RankTwoFive sk rs wk := by
  unfold BottomFive
  split <;>
    simp [Five,KingEntries,RookEntries,symX,sy,ry,dInf,absDiff] <;>
    simp only [square_eq_iff,Fin.ext_iff] <;>
    dsimp [RankTwoFive,KRKCanonicalSlots.left,KRKCanonicalSlots.right] <;>
    simp only [sy,and_true,true_and] <;> constructor <;> intro h <;> omega

end EndgameChess.Rules.KRKFiveMiddle
