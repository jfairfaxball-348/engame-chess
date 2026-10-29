import EndgameChess.Rules.KRKElevenNearStrip

namespace EndgameChess.Rules.KRKElevenInner
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

inductive Kind where
  | low | side | high

def king : Kind → Square
  | .low => (3,0)
  | .side => (3,1)
  | .high => (3,2)

def RookRegion (rs : Square) : Kind → Prop
  | .low => rs.2.val = 2 ∧ 3 ≤ rs.1.val
  | .side => (rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨
      (rs.1.val = 1 ∧ 3 ≤ rs.2.val ∧ rs.2.val ≤ 4) ∨ KRKNineNearStrip.RookCondition rs
  | .high => (rs.1.val = 2 ∧ rs.2.val = 2) ∨
      (rs.1.val = 1 ∧ 3 ≤ rs.2.val) ∨ (rs.2.val = 3 ∧ 3 ≤ rs.1.val)

def RookCondition (rs : Square) : Kind → Prop
  | .low => rs.2.val = 2 ∨ 3 ≤ rs.1.val
  | .side => True
  | .high => 3 ≤ rs.2.val ∨ (rs.1.val = 2 ∧ rs.2.val ≤ 1) ∨
      4 ≤ rs.1.val ∨ (rs.1.val = 0 ∧ rs.2.val = 2)

theorem horizontal_shape {sk rs : Square} : KRKTenInner.Horizontal sk rs ↔
    ∃ i : Kind, sk = king i ∧ RookRegion rs i := by
  constructor
  · intro region
    dsimp [KRKTenInner.Horizontal,KRKEightInner.Horizontal,KRKTenInner.SideExtra,KRKTenInner.HighExtra,KRKNineNearStrip.RookCondition] at region
    have choices : (sk = ((3 : Fin 8),0) ∧ RookRegion rs .low) ∨
        (sk = ((3 : Fin 8),1) ∧ RookRegion rs .side) ∨
        (sk = ((3 : Fin 8),2) ∧ RookRegion rs .high) := by
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp [RookRegion,KRKNineNearStrip.RookCondition]
      omega
    rcases choices with ⟨equal,shape⟩ | ⟨equal,shape⟩ | ⟨equal,shape⟩
    · exact ⟨.low,equal,shape⟩
    · exact ⟨.side,equal,shape⟩
    · exact ⟨.high,equal,shape⟩
  · rintro ⟨i,rfl,shape⟩
    cases i <;> dsimp [king,RookRegion,KRKNineNearStrip.RookCondition] at shape ⊢ <;>
      dsimp [KRKTenInner.Horizontal,KRKEightInner.Horizontal,KRKTenInner.SideExtra,KRKTenInner.HighExtra,KRKNineNearStrip.RookCondition] <;> omega

private theorem frame_f (s : Square) : (KRKElevenSlots.frame ((1 : Fin 8),1)).f s = s := rfl
private theorem frame_r (s : Square) : (KRKElevenSlots.frame ((1 : Fin 8),1)).r s = s := rfl

theorem global_region_iff {sk rs : Square} : KRKTenGlobal.Region sk rs (1,1) ↔ KRKTenInner.Region sk rs := by
  simp [KRKTenGlobal.Region,KRKTenInteriorExact.Region,KRKEightInteriorExact.stripFrame,
    KRKEdgeDepth.depth,Frame.ofSym,symId]

def KingEntry (sk rs ns : Square) : Prop := dInf sk ns = 1 ∧ ns ≠ rs ∧ KRKTenInner.Region ns rs

def KingEntries (sk rs : Square) : Prop :=
  (∃ i : Kind, KingEntry sk rs (king i)) ∨ (∃ i : Kind, KingEntry sk rs (symSwap.f (king i)))

theorem king_points_iff {sk rs : Square} : KRKElevenGeometry.KingPoints sk rs (1,1) ↔ KingEntries sk rs := by
  simp only [KRKElevenGeometry.KingPoints,frame_f,frame_r]
  constructor
  · rintro ⟨j,distance,apart,_,region⟩
    have inner := global_region_iff.mp region
    have entry : KingEntry sk rs (KRKElevenSlots.point j) := ⟨distance,apart,inner⟩
    rcases inner with horizontal | vertical
    · obtain ⟨i,equal,_⟩ := horizontal_shape.mp horizontal
      exact Or.inl ⟨i,equal ▸ entry⟩
    · obtain ⟨i,equal,_⟩ := horizontal_shape.mp vertical
      have actual : KRKElevenSlots.point j = symSwap.f (king i) := by simpa only [symSwap.invol] using congrArg symSwap.f equal
      exact Or.inr ⟨i,actual ▸ entry⟩
  · intro entries
    have fromEntry : ∀ {ns : Square}, KingEntry sk rs ns → KRKElevenGeometry.KingPoints sk rs (1,1) := by
      intro ns entry
      have region := global_region_iff.mpr entry.2.2
      have far : 2 ≤ dInf ns ((1 : Fin 8),1) := by
        have inner := entry.2.2
        dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,KRKTenInner.SideExtra,KRKTenInner.HighExtra,symSwap,dInf,absDiff] at inner ⊢
        omega
      obtain ⟨j,equal⟩ := KRKElevenSlots.region_point region
      rw [frame_f] at equal
      simp only [KRKElevenGeometry.KingPoints,frame_f,frame_r]
      exact ⟨j,equal ▸ entry.1,equal ▸ entry.2.1,equal ▸ far,equal ▸ region⟩
    rcases entries with ⟨i,entry⟩ | ⟨i,entry⟩
    all_goals exact fromEntry entry

private theorem not_file_one {rs : Square} {i : Kind} (notWeak : rs ≠ ((1 : Fin 8),1))
    (notCheck : ¬RookSees rs (1,1) (king i) (1,1)) : rs.1.val ≠ 1 := by
  cases i <;> simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at notWeak notCheck <;>
    dsimp at notWeak notCheck <;> omega

theorem rook_line_necessary {rs nr : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((1 : Fin 8),1)) (notCheck : ¬RookSees rs (1,1) (king i) (1,1))
    (sees : RookSees rs nr (king i) (1,1)) (region : RookRegion nr i) : RookCondition rs i := by
  have notOne := not_file_one notWeak notCheck
  cases i with
  | low => exact KRKNineInner.rook_line_necessary (i := .low) apart notWeak notCheck sees region
  | side => exact True.intro
  | high =>
    rcases region with diagonal | file | row
    all_goals
      have line := sees.1.2
      rcases line with vertical | horizontal
    all_goals
      dsimp [RookCondition] at *
      simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] at apart sees
      dsimp at apart sees
      omega

theorem rook_destination {rs : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((1 : Fin 8),1)) (notCheck : ¬RookSees rs (1,1) (king i) (1,1))
    (condition : RookCondition rs i) : ∃ nr, RookSees rs nr (king i) (1,1) ∧ RookRegion nr i := by
  have notOne := not_file_one notWeak notCheck
  cases i with
  | low => exact KRKNineInner.rook_destination (i := .low) apart notWeak notCheck condition
  | side =>
    let nr : Square := if rs.2.val = 3 then (if rs.1.val = 4 then 5 else 4,3)
      else if rs.1.val = 3 ∧ rs.2.val ≤ 1 then (4,rs.2) else (rs.1,3)
    refine ⟨nr,?_,?_⟩
    · dsimp [nr]; split <;> (try split) <;> (try split) <;>
        simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] <;> (try simp) <;> omega
    · dsimp [nr]; split <;> (try split) <;> (try split) <;>
        dsimp [RookRegion,KRKNineNearStrip.RookCondition] <;> (try simp) <;> omega
  | high =>
    let nr : Square := if 3 ≤ rs.2.val then (1,rs.2)
      else if 4 ≤ rs.1.val then (rs.1,3) else (2,2)
    refine ⟨nr,?_,?_⟩
    · dsimp [nr]; split <;> (try split) <;>
        simp only [king,RookSees,RookLine,OnSeg,ne_iff_coords] <;>
        dsimp [RookCondition] at condition <;> (try simp) <;> omega
    · dsimp [nr]; split <;> (try split) <;> dsimp [RookRegion,RookCondition] at * <;> (try simp) <;> omega

def RookEntries (sk rs : Square) : Prop :=
  (∃ i : Kind, sk = king i ∧ RookCondition rs i) ∨
  (∃ i : Kind, symSwap.f sk = king i ∧ RookCondition (symSwap.f rs) i)

theorem rook_rays_necessary {sk rs : Square} (apart : sk ≠ rs) (notWeak : rs ≠ ((1 : Fin 8),1))
    (notCheck : ¬RookSees rs (1,1) sk (1,1)) (rays : KRKElevenGeometry.RookRays sk rs (1,1)) : RookEntries sk rs := by
  simp only [KRKElevenGeometry.RookRays,frame_f,frame_r] at rays
  obtain ⟨_,_,a,v,sees,_,_,region⟩ := rays
  rcases global_region_iff.mp region with horizontal | vertical
  · obtain ⟨i,equal,condition⟩ := horizontal_shape.mp horizontal
    exact Or.inl ⟨i,equal,rook_line_necessary (equal ▸ apart) notWeak (equal ▸ notCheck) (equal ▸ sees) condition⟩
  · obtain ⟨i,equal,condition⟩ := horizontal_shape.mp vertical
    have mappedSees := (symSwap.sees_iff _ _ _ _).mpr sees
    have mappedCheck : ¬RookSees (symSwap.f rs) (1,1) (symSwap.f sk) (1,1) :=
      fun h => notCheck ((symSwap.sees_iff _ _ _ _).mp h)
    rw [show symSwap.f ((1 : Fin 8),1) = ((1 : Fin 8),1) from rfl,equal] at mappedSees
    rw [equal] at mappedCheck
    exact Or.inr ⟨i,equal,rook_line_necessary (equal ▸ (symSwap.ne_iff.mpr apart))
      (symSwap.ne_iff.mpr notWeak) mappedCheck mappedSees condition⟩

theorem canonical_rook_clear {rs : Square} {i : Kind} (apart : king i ≠ rs)
    (notWeak : rs ≠ ((1 : Fin 8),1)) (notCheck : ¬RookSees rs (1,1) (king i) (1,1))
    (condition : RookCondition rs i) : KRKElevenGeometry.Clear (king i) rs (1,1) := by
  obtain ⟨nr,sees,region⟩ := rook_destination apart notWeak notCheck condition
  have global := global_region_iff.mpr (Or.inl (horizontal_shape.mpr ⟨i,rfl,region⟩))
  apply KRKElevenGeometry.rook_step_clear sees ?_ ?_ global
  · cases i <;> dsimp [RookRegion,KRKNineNearStrip.RookCondition] at region <;> simp only [king,ne_iff_coords] <;> dsimp <;> omega
  · cases i <;> dsimp [RookRegion,KRKNineNearStrip.RookCondition] at region <;> simp only [ne_iff_coords] <;> dsimp <;> omega

def Eleven (sk rs : Square) : Prop := KingEntries sk rs ∨ RookEntries sk rs

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (notKing : sk ≠ ((1 : Fin 8),1))
    (notWeak : rs ≠ ((1 : Fin 8),1)) (far : 2 ≤ dInf sk (1,1)) (notCheck : ¬RookSees rs (1,1) sk (1,1)) :
    KRKElevenGeometry.Clear sk rs (1,1) ↔ Eleven sk rs := by
  constructor
  · rintro (immediate | points | rays)
    · have zero := KRKFourPlyEscape.three_depth_zero (Or.inl immediate)
      change 1 = 0 at zero
      contradiction
    · exact Or.inl (king_points_iff.mp points)
    · exact Or.inr (rook_rays_necessary apart notWeak notCheck rays)
  · rintro (points | (⟨i,equal,condition⟩ | ⟨i,equal,condition⟩))
    · exact Or.inr (Or.inl (king_points_iff.mpr points))
    · rw [equal] at apart notCheck ⊢
      exact canonical_rook_clear apart notWeak notCheck condition
    · let g := Frame.ofSym symSwap
      have mappedApart : king i ≠ g.f rs := equal ▸ g.ne_iff.mpr apart
      have mappedCheck : ¬RookSees (g.f rs) (1,1) (king i) (1,1) := by
        rw [←equal]
        exact fun h => notCheck ((g.sees _ _ _ _).mp h)
      have mapped := canonical_rook_clear mappedApart (g.ne_iff.mpr notWeak) mappedCheck condition
      rw [←equal] at mapped
      have back := KRKElevenGeometry.frame_map g (g.ne_iff.mpr apart) (g.ne_iff.mpr notKing) (g.ne_iff.mpr notWeak)
        (by rw [g.distance]; exact far) (fun h => notCheck ((g.sees _ _ _ _).mp h)) mapped
      simpa only [g,Frame.ofSym,symSwap.invol,show symSwap.f ((1 : Fin 8),1) = ((1 : Fin 8),1) from rfl] using back

theorem kernel_eleven_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,1))
    (notCheck : ¬RookSees rs (1,1) sk (1,1)) : MateWithin σ 11 q ↔ Eleven sk rs :=
  (KRKElevenGeometry.kernel_eleven_iff material turn far notCheck).trans
    (clear_iff material.1 material.2.1 material.2.2.1 far notCheck)

theorem kernel_exact_eleven {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,1))
    (notCheck : ¬RookSees rs (1,1) sk (1,1)) :
    (MateWithin σ 11 q ∧ ¬MateWithin σ 10 q) ↔ Eleven sk rs ∧ ¬KRKNineInner.Nine sk rs := by
  constructor
  · rintro ⟨eleven,notTen⟩
    refine ⟨(kernel_eleven_iff material turn far notCheck).mp eleven,?_⟩
    intro nine
    exact notTen (mateWithin_mono ((KRKNineInner.kernel_nine_iff material turn far notCheck).mpr nine) (by decide))
  · rintro ⟨region,notNine⟩
    refine ⟨(kernel_eleven_iff material turn far notCheck).mpr region,?_⟩
    intro ten
    exact notNine ((KRKNineInner.kernel_nine_iff material turn far notCheck).mp
      (KRKTenGeometry.strong_ten_nine material turn ten))

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),1))
    (apart : sk ≠ rs) (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) :
    KRKElevenGeometry.Clear sk rs wk ↔ Eleven (g.f sk) (g.f rs) := by
  have notKing : sk ≠ wk := ne_of_dInf_pos (by omega)
  constructor
  · intro clear
    have mapped := KRKElevenGeometry.frame_map g apart notKing notRook far notCheck clear
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    rw [target] at mapped mappedFar
    exact (clear_iff (g.ne_iff.mpr apart) (target ▸ g.ne_iff.mpr notKing)
      (target ▸ g.ne_iff.mpr notRook) mappedFar
      (fun h => notCheck ((g.sees _ _ _ _).mp (by simpa only [target] using h)))).mp mapped
  · intro region
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    have mapped := (clear_iff (g.ne_iff.mpr apart) (target ▸ g.ne_iff.mpr notKing)
      (target ▸ g.ne_iff.mpr notRook) (target ▸ mappedFar)
      (fun h => notCheck ((g.sees _ _ _ _).mp (by simpa only [target] using h)))).mpr region
    have shaped : KRKElevenGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr apart)
      (g.ne_iff.mpr notKing) (g.ne_iff.mpr notRook) (by rw [g.distance]; exact far)
      (fun h => notCheck ((g.sees _ _ _ _).mp (by simpa only [target] using h))) shaped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKElevenInner
