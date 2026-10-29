import EndgameChess.Rules.KRKSevenSecond

namespace EndgameChess.Rules.KRKSevenCorner
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

inductive Kind where
  | west | near | diagonal | highWest | highNear | highMiddle | highDiagonal

def king : Kind → Square
  | .west => (0,2)
  | .near => (1,2)
  | .diagonal => (2,2)
  | .highWest => (0,3)
  | .highNear => (1,3)
  | .highMiddle => (2,3)
  | .highDiagonal => (3,3)

def RookCondition (rs : Square) : Kind → Prop
  | .west | .near | .diagonal => True
  | .highWest => rs.2.val = 1 ∨ rs.1.val = 2 ∨ rs.1.val = 3
  | .highNear => rs.2.val = 1 ∨ 2 ≤ rs.1.val
  | .highMiddle => 1 ≤ rs.1.val ∨ rs.2.val = 1 ∨ 4 ≤ rs.2.val
  | .highDiagonal => rs.1.val = 1 ∨ rs.2.val = 1 ∨ 4 ≤ rs.1.val ∨ 4 ≤ rs.2.val

def LiveTest (sk rs : Square) : Prop :=
  KRKCornerWeakBand.Guard sk rs (0,0) (0,1) ∨
  KRKCornerWeakBand.Guard sk rs (0,0) (1,0) ∨
  KRKCornerWeakBand.Guard sk rs (0,0) (1,1)

theorem live_iff {sk rs : Square} : KRKSevenGeometry.Live sk rs (0,0) ↔ LiveTest sk rs := by
  constructor
  · rintro ⟨t,guard⟩
    have choices : t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),1) := by
      have distance := guard.1
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp [dInf,absDiff] at distance
      dsimp
      omega
    rcases choices with rfl | rfl | rfl
    · exact Or.inl guard
    · exact Or.inr (Or.inl guard)
    · exact Or.inr (Or.inr guard)
  · rintro (guard | guard | guard)
    all_goals exact ⟨_,guard⟩

theorem frame_f (s : Square) : (KRKSevenSlots.frame ((0 : Fin 8),0)).f s = s := by
  simp [KRKSevenSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId]

theorem frame_r (s : Square) : (KRKSevenSlots.frame ((0 : Fin 8),0)).r s = s := by
  simp [KRKSevenSlots.frame,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId]

theorem global_region_iff {sk rs : Square} : KRKSixGlobal.Region sk rs (0,0) ↔ KRKSixCorner.Region sk rs := by
  simp [KRKSixGlobal.Region,KRKEdgeDepth.depth,normalize,bottomFrame,Frame.ofSym,symId,KRKSixGlobal.EdgeRegion]

theorem region_point {sk rs : Square} (region : KRKSixCorner.Region sk rs) :
    (∃ i, sk = king i) ∨ (∃ i, symSwap.f sk = king i) := by
  rcases region with ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩ | ⟨sx,sy⟩ |
    ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩ | ⟨sx,sy,_⟩
  · exact Or.inl ⟨.west,Prod.ext (Fin.ext sx) (Fin.ext sy)⟩
  · exact Or.inr ⟨.west,Prod.ext (Fin.ext sy) (Fin.ext sx)⟩
  · exact Or.inl ⟨.near,Prod.ext (Fin.ext sx) (Fin.ext sy)⟩
  · exact Or.inr ⟨.near,Prod.ext (Fin.ext sy) (Fin.ext sx)⟩
  · exact Or.inl ⟨.diagonal,Prod.ext (Fin.ext sx) (Fin.ext sy)⟩
  · exact Or.inl ⟨.highWest,Prod.ext (Fin.ext sx) (Fin.ext sy)⟩
  · exact Or.inr ⟨.highWest,Prod.ext (Fin.ext sy) (Fin.ext sx)⟩
  · rcases sx with sx | sx
    · exact Or.inl ⟨.highNear,Prod.ext (Fin.ext sx) (Fin.ext sy)⟩
    · exact Or.inl ⟨.highMiddle,Prod.ext (Fin.ext sx) (Fin.ext sy)⟩
  · rcases sy with sy | sy
    · exact Or.inr ⟨.highNear,Prod.ext (Fin.ext sy) (Fin.ext sx)⟩
    · exact Or.inr ⟨.highMiddle,Prod.ext (Fin.ext sy) (Fin.ext sx)⟩
  · exact Or.inl ⟨.highDiagonal,Prod.ext (Fin.ext sx) (Fin.ext sy)⟩

def KingEntry (sk rs ns : Square) : Prop :=
  dInf sk ns = 1 ∧ ns ≠ rs ∧ KRKSixCorner.Region ns rs ∧ LiveTest ns rs ∧ SafeRook ns rs (0,0)

def KingEntries (sk rs : Square) : Prop :=
  (∃ i : Kind, KingEntry sk rs (king i)) ∨
  (∃ i : Kind, KingEntry sk rs (symSwap.f (king i)))

theorem king_points_iff {sk rs : Square} : KRKSevenGeometry.KingPoints sk rs (0,0) ↔ KingEntries sk rs := by
  simp only [KRKSevenGeometry.KingPoints,frame_f,frame_r]
  constructor
  · rintro ⟨j,distance,apart,_,region,live,safe⟩
    have corner := global_region_iff.mp region
    have entry : KingEntry sk rs (KRKSevenSlots.point j) := ⟨distance,apart,corner,live_iff.mp live,safe⟩
    rcases region_point corner with ⟨i,equal⟩ | ⟨i,equal⟩
    · exact Or.inl ⟨i,equal ▸ entry⟩
    · have actual : KRKSevenSlots.point j = symSwap.f (king i) := by
        simpa only [symSwap.invol] using congrArg symSwap.f equal
      exact Or.inr ⟨i,actual ▸ entry⟩
  · intro entries
    have fromEntry : ∀ {ns : Square}, KingEntry sk rs ns → KRKSevenGeometry.KingPoints sk rs (0,0) := by
      intro ns entry
      have far : 2 ≤ dInf ns ((0 : Fin 8),0) := by
        have region := entry.2.2.1
        dsimp [KRKSixCorner.Region,dInf,absDiff] at *
        omega
      have global := global_region_iff.mpr entry.2.2.1
      obtain ⟨j,equal⟩ := KRKSevenSlots.region_point global
      rw [frame_f] at equal
      simp only [KRKSevenGeometry.KingPoints,frame_f,frame_r]
      exact ⟨j,equal ▸ entry.1,equal ▸ entry.2.1,equal ▸ far,
        equal ▸ global,equal ▸ live_iff.mpr entry.2.2.2.1,equal ▸ entry.2.2.2.2⟩
    rcases entries with ⟨i,entry⟩ | ⟨i,entry⟩
    all_goals exact fromEntry entry

theorem rook_line_necessary {rs nr : Square} {i : Kind} (apart : king i ≠ rs)
    (sees : RookSees rs nr (king i) (0,0)) (region : KRKSixCorner.Region (king i) nr) :
    RookCondition rs i := by
  cases i <;> dsimp [RookCondition] <;> (try trivial)
  all_goals
    simp only [king,KRKSixCorner.Region,RookSees,RookLine,OnSeg,ne_iff_coords] at sees region apart
    (try dsimp at sees region apart)
    omega

private def target (i : Kind) (rs : Square) : Square :=
  match i with
  | .west | .near => (if rs.1.val = 2 then 3 else 2,rs.2)
  | .diagonal => (3,3)
  | .highWest | .highNear =>
    if rs.2.val = 1 then (if rs.1.val = 2 then 3 else 2,1) else (rs.1,1)
  | .highMiddle =>
    if rs.2.val = 1 then (if rs.1.val = 2 then 3 else 2,1)
    else if rs.1.val = 1 then (1,if rs.2.val = 4 then 5 else 4)
    else if 4 ≤ rs.2.val then (1,rs.2) else (rs.1,1)
  | .highDiagonal =>
    if rs.1.val = 1 then (1,if rs.2.val = 4 then 5 else 4)
    else if 4 ≤ rs.2.val then (1,rs.2)
    else if rs.2.val = 1 then (if rs.1.val = 4 then 5 else 4,1) else (rs.1,1)

theorem rook_destination {rs : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((0 : Fin 8),0)) (notCheck : ¬RookSees rs (0,0) (king i) (0,0))
    (condition : RookCondition rs i) :
    ∃ nr, RookSees rs nr (king i) (0,0) ∧ nr ≠ king i ∧
      KRKSixCorner.Region (king i) nr ∧ KRKSevenGeometry.Live (king i) nr (0,0) ∧
        SafeRook (king i) nr (0,0) := by
  by_cases diagonal : i = .diagonal
  · subst i
    obtain ⟨a,v,sees,region⟩ := KRKFiveCornerEntries.corner22_reachable apart notWeak notCheck
    obtain ⟨distinct,live,safe⟩ := KRKFiveCornerEntries.slot22_properties region
    refine ⟨a.target rs v,sees,distinct.symm,?_,live,safe⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))))
  have height : 1 ≤ rs.2.val := by
    cases i <;> simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at notWeak notCheck <;>
      dsimp at notWeak notCheck <;> omega
  refine ⟨target i rs,?_,?_,?_,?_,?_⟩
  · cases i <;> (try contradiction) <;>
      dsimp [target] <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at apart notCheck ⊢ <;>
      dsimp [RookCondition] at condition <;> (try simp at apart notCheck ⊢) <;> omega
  · cases i <;> (try contradiction) <;>
      dsimp [target] <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      simp only [king,ne_iff_coords] <;> dsimp [RookCondition] at condition <;> (try simp) <;> omega
  · cases i <;> (try contradiction) <;>
      dsimp [target] <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      simp only [king,KRKSixCorner.Region] <;> dsimp [RookCondition] at condition <;> (try simp) <;> omega
  · let t : Square := if (target i rs).1.val = 1 then (0,1) else (1,0)
    refine ⟨t,?_⟩
    cases i <;> (try contradiction) <;>
      dsimp [t,target] <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      simp only [king,KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] <;>
      dsimp [RookCondition] at condition <;> (try simp_all [king,target]) <;> omega
  · apply Or.inl
    cases i <;> (try contradiction) <;>
      dsimp [target] <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      dsimp [dInf,absDiff,RookCondition] at condition ⊢ <;> omega

def RookEntries (sk rs : Square) : Prop :=
  (∃ i : Kind, sk = king i ∧ RookCondition rs i) ∨
  (∃ i : Kind, symSwap.f sk = king i ∧ RookCondition (symSwap.f rs) i)

theorem rook_rays_necessary {sk rs : Square} (apart : sk ≠ rs)
    (rays : KRKSevenGeometry.RookRays sk rs (0,0)) : RookEntries sk rs := by
  simp only [KRKSevenGeometry.RookRays,frame_f,frame_r] at rays
  obtain ⟨_,_,a,v,sees,_,_,region,_,_⟩ := rays
  have corner := global_region_iff.mp region
  rcases region_point corner with ⟨i,equal⟩ | ⟨i,equal⟩
  · exact Or.inl ⟨i,equal,rook_line_necessary (equal ▸ apart) (equal ▸ sees) (equal ▸ corner)⟩
  · have mapped := (symSwap.sees_iff _ _ _ _).mpr sees
    have mappedRegion := KRKSixCorner.region_swap.mpr corner
    rw [show symSwap.f ((0 : Fin 8),0) = ((0 : Fin 8),0) from rfl,equal] at mapped
    rw [equal] at mappedRegion
    exact Or.inr ⟨i,equal,rook_line_necessary (equal ▸ (symSwap.ne_iff.mpr apart)) mapped mappedRegion⟩

theorem canonical_rook_clear {rs : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((0 : Fin 8),0)) (notCheck : ¬RookSees rs (0,0) (king i) (0,0))
    (condition : RookCondition rs i) : KRKSevenGeometry.Clear (king i) rs (0,0) := by
  obtain ⟨nr,sees,distinct,region,live,safe⟩ := rook_destination apart notWeak notCheck condition
  apply KRKSevenReach.rook_step_clear sees distinct
  · intro equal
    have zero : dInf nr ((0 : Fin 8),0) = 0 := by rw [equal]; decide
    have far : 2 ≤ dInf (king i) (0,0) := by cases i <;> decide
    dsimp [SafeRook,dInf,absDiff] at safe far zero
    omega
  · exact global_region_iff.mpr region
  · exact live
  · exact safe

theorem rook_entries_sufficient {sk rs : Square} (apart : sk ≠ rs) (notKing : sk ≠ ((0 : Fin 8),0))
    (notWeak : rs ≠ ((0 : Fin 8),0)) (far : 2 ≤ dInf sk (0,0))
    (notCheck : ¬RookSees rs (0,0) sk (0,0)) (entries : RookEntries sk rs) :
    KRKSevenGeometry.Clear sk rs (0,0) := by
  rcases entries with ⟨i,equal,condition⟩ | ⟨i,equal,condition⟩
  · rw [equal] at apart notCheck ⊢
    exact canonical_rook_clear apart notWeak notCheck condition
  · let g := Frame.ofSym symSwap
    have mappedApart : king i ≠ g.f rs := equal ▸ g.ne_iff.mpr apart
    have mappedNotWeak : g.f rs ≠ ((0 : Fin 8),0) := g.ne_iff.mpr notWeak
    have mappedNotCheck : ¬RookSees (g.f rs) (0,0) (king i) (0,0) := by
      rw [←equal]
      exact fun h => notCheck ((g.sees _ _ _ _).mp h)
    have mapped := canonical_rook_clear mappedApart mappedNotWeak mappedNotCheck condition
    rw [←equal] at mapped
    have back := KRKSevenReach.frame_map g (g.ne_iff.mpr apart) (g.ne_iff.mpr notKing)
      (g.ne_iff.mpr notWeak) (by rw [g.distance]; exact far)
      (fun h => notCheck ((g.sees _ _ _ _).mp h)) mapped
    simpa only [g,Frame.ofSym,symSwap.invol,show symSwap.f ((0 : Fin 8),0) = ((0 : Fin 8),0) from rfl] using back

theorem immediate_entries {sk rs : Square} (immediate : KRKImmediate.MateNow sk rs (0,0)) :
    RookEntries sk rs := by
  have shape : (sk.2.val = 2 ∧ sk.1.val ≤ 1) ∨ (sk.1.val = 2 ∧ sk.2.val ≤ 1) := by
    simp only [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate
    dsimp at immediate
    omega
  rcases shape with ⟨sy,sx⟩ | ⟨sx,sy⟩
  · by_cases zero : sk.1.val = 0
    · exact Or.inl ⟨.west,Prod.ext (Fin.ext zero) (Fin.ext sy),True.intro⟩
    · exact Or.inl ⟨.near,Prod.ext (Fin.ext (by change sk.1.val = 1; omega)) (Fin.ext sy),True.intro⟩
  · by_cases zero : sk.2.val = 0
    · exact Or.inr ⟨.west,Prod.ext (Fin.ext zero) (Fin.ext sx),True.intro⟩
    · exact Or.inr ⟨.near,Prod.ext (Fin.ext (by change sk.2.val = 1; omega)) (Fin.ext sx),True.intro⟩

/-- Twelve distinct king destinations and evaluated rook-line conditions.
The two diagonal points occur in both orientations of the catalogue. -/
def Seven (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (notKing : sk ≠ ((0 : Fin 8),0))
    (notWeak : rs ≠ ((0 : Fin 8),0)) (far : 2 ≤ dInf sk (0,0))
    (notCheck : ¬RookSees rs (0,0) sk (0,0)) : KRKSevenGeometry.Clear sk rs (0,0) ↔ Seven sk rs := by
  constructor
  · rintro (immediate | points | rays)
    · exact Or.inr (immediate_entries immediate)
    · exact Or.inl (king_points_iff.mp points)
    · exact Or.inr (rook_rays_necessary apart rays)
  · rintro (points | entries)
    · exact Or.inr (Or.inl (king_points_iff.mpr points))
    · exact rook_entries_sufficient apart notKing notWeak far notCheck entries

theorem kernel_seven_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (0,0)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (0,0))
    (notCheck : ¬RookSees rs (0,0) sk (0,0)) : MateWithin σ 7 q ↔ Seven sk rs :=
  (KRKSevenGeometry.kernel_seven_iff material turn far notCheck).trans
    (clear_iff material.1 material.2.1 material.2.2.1 far notCheck)

end EndgameChess.Rules.KRKSevenCorner
