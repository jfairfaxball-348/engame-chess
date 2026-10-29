import EndgameChess.Rules.KRKEightDiagonalEntries

namespace EndgameChess.Rules.KRKTenInner
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def SideExtra (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 1 ∧ KRKNineNearStrip.RookCondition rs

def HighExtra (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.2.val = 3 ∧ 3 ≤ rs.1.val

def Horizontal (sk rs : Square) : Prop := KRKEightInner.Horizontal sk rs ∨ SideExtra sk rs ∨ HighExtra sk rs

def Region (sk rs : Square) : Prop := Horizontal sk rs ∨ Horizontal (symSwap.f sk) (symSwap.f rs)

private theorem blocked_covered {sk rs wk t : Square} (safe : SafeRook sk rs wk) (distance : dInf wk t = 1)
    (blocked : ¬KRKCornerWeakBand.Guard sk rs wk t) : Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  exact False.elim (blocked ⟨distance,notRook,by omega,fun sees => line sees.1⟩)

theorem near_guard_necessary {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKTenGeometry.Clear sk rs (1,1)) (guard : KRKCornerWeakBand.Guard sk rs (1,1) (1,2)) :
    Horizontal sk rs := by
  have condition := (KRKNineNearStrip.clear_iff distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
    guard.2.1.symm guard.2.2.1 guard.2.2.2).mp (clear.2.2 _ guard)
  rcases condition with ⟨row,width,distance⟩ | ⟨king,rook⟩
  · have cover := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,2))
      (by decide) (Or.inl (by decide)))
    have shape : sk.1.val = 3 ∧ (sk.2.val = 1 ∨ sk.2.val = 2) := by
      dsimp [dInf,absDiff] at far distance
      dsimp at cover
      omega
    rcases shape.2 with one | two
    · exact Or.inr (Or.inl ⟨shape.1,one,Or.inl row⟩)
    · exact Or.inr (Or.inr ⟨shape.1,two,row,width⟩)
  · have sx := congrArg (fun s : Square => s.1.val) king
    have sy := congrArg (fun s : Square => s.2.val) king
    exact Or.inr (Or.inl ⟨sx,sy,rook⟩)

private theorem row_two_necessary {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val ≤ 2) (ry : rs.2.val = 2) (clear : KRKTenGeometry.Clear sk rs (1,1))
    (blocked : ¬KRKCornerWeakBand.Guard sk rs (1,1) (1,2)) : KRKEightInner.Horizontal sk rs := by
  have safe := clear.1
  have width : 2 ≤ rs.1.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
  have low : sk.2.val = 0 → 3 ≤ rs.1.val := by
    intro zero
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have high : sk.2.val = 2 → rs.1.val = 2 := by
    intro two
    by_cases equal : rs.1.val = 2
    · exact equal
    apply False.elim
    have notThree : rs.1.val ≠ 3 := by
      intro three
      exact distinct (Prod.ext (Fin.ext (sx.trans three.symm)) (Fin.ext (two.trans ry.symm)))
    apply blocked
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,two,ry]
    simp <;> omega
  dsimp [KRKEightInner.Horizontal]
  omega

private theorem file_one_necessary {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 1 ∨ sk.2.val = 2) (rx : rs.1.val = 1) (clear : KRKTenGeometry.Clear sk rs (1,1)) :
    KRKEightInner.Horizontal sk rs := by
  have height : 3 ≤ rs.2.val := by have safe := clear.1; dsimp [SafeRook,dInf,absDiff] at safe; omega
  rcases sy with one | two
  · have upper : rs.2.val ≤ 4 := by
      by_cases short : rs.2.val ≤ 4
      · exact short
      apply False.elim
      have guard : KRKCornerWeakBand.Guard sk rs (1,1) (0,2) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,one,rx]
        simp <;> omega
      let g := Frame.ofSym symSwap
      have mapped := KRKNineGeometry.frame_map g distinct
        (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2 (clear.2.2 _ guard)
      have king : g.f sk = ((1 : Fin 8),3) := Prod.ext (Fin.ext one) (Fin.ext sx)
      rw [king] at mapped
      exact KRKNineSecondLeft.no_nine (rs := g.f rs) (by dsimp [g,Frame.ofSym,symSwap]; omega) rx mapped
    exact ⟨sx,Or.inr (Or.inl ⟨one,Or.inr ⟨rx,height,upper⟩⟩)⟩
  · exact ⟨sx,Or.inr (Or.inr ⟨two,Or.inr ⟨rx,height⟩⟩)⟩

private theorem swap_guard {sk rs : Square}
    (guard : KRKCornerWeakBand.Guard (symSwap.f sk) (symSwap.f rs) (1,1) (1,2)) :
    KRKCornerWeakBand.Guard sk rs (1,1) (2,1) := by
  have step := (Frame.ofSym symSwap).map_step (StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2)
  have back := KRKCornerWeakBand.step_guard step
  simpa only [Frame.ofSym,symSwap.invol,show symSwap.f ((1 : Fin 8),1) = ((1 : Fin 8),1) from rfl,
    show symSwap.f ((1 : Fin 8),2) = ((2 : Fin 8),1) from rfl] using back

private theorem diagonal_no_clear : ¬KRKTenGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) (1,1) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),3) ((2 : Fin 8),2) (1,1) (1,0) := by
    simp [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] <;> omega
  exact KRKNineNearDiagonal.no_nine (clear.2.2 _ guard)

theorem necessary {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKTenGeometry.Clear sk rs (1,1)) : Region sk rs := by
  by_cases near : KRKCornerWeakBand.Guard sk rs (1,1) (1,2)
  · exact Or.inl (near_guard_necessary distinct far clear near)
  have mapped := KRKTenGeometry.frame_map (Frame.ofSym symSwap) distinct clear
  have mappedFar : 2 ≤ dInf (symSwap.f sk) ((1 : Fin 8),1) := by
    change 2 ≤ dInf (symSwap.f sk) (symSwap.f ((1 : Fin 8),1))
    rw [symSwap.dInf_eq]
    exact far
  by_cases other : KRKCornerWeakBand.Guard sk rs (1,1) (2,1)
  · have step := (Frame.ofSym symSwap).map_step (StepM.lone other.1 other.2.1 other.2.2.1 other.2.2.2)
    have guard := KRKCornerWeakBand.step_guard step
    have actual : KRKCornerWeakBand.Guard (symSwap.f sk) (symSwap.f rs) (1,1) (1,2) := by
      simpa only [Frame.ofSym,show symSwap.f ((1 : Fin 8),1) = ((1 : Fin 8),1) from rfl,
        show symSwap.f ((2 : Fin 8),1) = ((1 : Fin 8),2) from rfl] using guard
    exact Or.inr (near_guard_necessary (symSwap.ne_iff.mpr distinct) mappedFar mapped actual)
  have cover : ∀ t, dInf ((1 : Fin 8),1) t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t := by
    intro t distance inside
    have targets : t = ((1 : Fin 8),2) ∨ t = ((2 : Fin 8),1) ∨ t = ((2 : Fin 8),2) := by
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp [dInf,absDiff] at distance
      dsimp [KRKEdgeDepth.depth] at inside
      dsimp
      omega
    rcases targets with rfl | rfl | rfl
    · exact blocked_covered clear.1 (by decide) near
    · exact blocked_covered clear.1 (by decide) other
    · exact KRKTenSecondCorner.bad_neighbour_covered distinct clear (by decide) (Or.inl (by decide))
  have mappedBlocked : ¬KRKCornerWeakBand.Guard (symSwap.f sk) (symSwap.f rs) (1,1) (1,2) := fun h => other (swap_guard h)
  rcases corner_prison rfl rfl far clear.1 cover with
    ⟨sx,sy,ry⟩ | ⟨sy,sx,rx⟩ | ⟨sx,sy,rx⟩ | ⟨sy,sx,ry⟩ | ⟨sx,sy,rx,ry⟩
  · exact Or.inl (Or.inl (row_two_necessary distinct sx sy ry clear near))
  · exact Or.inr (Or.inl (row_two_necessary (symSwap.ne_iff.mpr distinct) sy sx rx mapped mappedBlocked))
  · exact Or.inl (Or.inl (file_one_necessary distinct sx sy rx clear))
  · exact Or.inr (Or.inl (file_one_necessary (symSwap.ne_iff.mpr distinct) sy sx ry mapped))
  · have king : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rook : rs = ((2 : Fin 8),2) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    rw [king,rook] at clear
    exact False.elim (diagonal_no_clear clear)

private theorem swap_diagonal_entry {sk rs t : Square} (distinct : sk ≠ rs)
    (guard : KRKCornerWeakBand.Guard sk rs (1,1) t)
    (apart : ((2 : Fin 8),2) ≠ symSwap.f rs)
    (distance : dInf (symSwap.f sk) (2,2) = 1) (far : 2 ≤ dInf ((2 : Fin 8),2) (symSwap.f t))
    (region : KRKEightGlobal.Region (2,2) (symSwap.f rs) (symSwap.f t)) : KRKNineGeometry.Clear sk rs t := by
  let g := Frame.ofSym symSwap
  have mapped := KRKNineGeometry.king_step_clear distance apart far region
  have back := KRKNineGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
    (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega))) (g.ne_iff.mpr guard.2.1.symm)
    (by rw [g.distance]; exact guard.2.2.1) (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
  simpa only [g,Frame.ofSym,Frame.inverse,symSwap.invol] using back

private theorem corner_apart {rs : Square} (far : 3 ≤ dInf rs (0,0)) : ((2 : Fin 8),2) ≠ rs := by
  intro equal
  rw [←equal] at far
  change 3 ≤ 2 at far
  omega

theorem side_extra_clear {sk rs : Square} (region : SideExtra sk rs) : KRKTenGeometry.Clear sk rs (1,1) := by
  obtain ⟨sx,sy,rook⟩ := region
  have distinct : sk ≠ rs := by
    dsimp [KRKNineNearStrip.RookCondition] at rook
    simp only [ne_iff_coords,sx,sy]
    omega
  have farR : 3 ≤ dInf rs (0,0) := by dsimp [KRKNineNearStrip.RookCondition,dInf,absDiff] at *; omega
  have apart := corner_apart farR
  have safe : SafeRook sk rs (1,1) := by dsimp [KRKNineNearStrip.RookCondition,SafeRook,dInf,absDiff] at *; omega
  have live : ∃ t,KRKCornerWeakBand.Guard sk rs (1,1) t := by
    by_cases side : rs.1.val = 0 ∨ rs.2.val = 1
    · refine ⟨((1 : Fin 8),0),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy]
      dsimp [KRKNineNearStrip.RookCondition] at rook
      simp <;> omega
    · refine ⟨((0 : Fin 8),1),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy]
      simp <;> omega
  refine ⟨safe,live,?_⟩
  intro t guard
  have targets : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨
      t = ((1 : Fin 8),0) ∨ t = ((1 : Fin 8),2) := by
    have distance := guard.1
    have separate := guard.2.2.1
    simp only [square_eq_iff,Fin.ext_iff]
    dsimp [dInf,absDiff] at distance separate
    dsimp
    omega
  rcases targets with rfl | rfl | rfl | rfl | rfl
  · apply KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) ?_ apart (by decide)
      (KRKEightDiagonalEntries.corner_region farR)
    dsimp [dInf,absDiff]; omega
  · refine swap_diagonal_entry distinct guard (by exact (Frame.ofSym symSwap).ne_iff.mpr apart) ?_ (by decide) ?_
    · dsimp [symSwap,dInf,absDiff]; omega
    · apply KRKEightDiagonalEntries.near_region ((Frame.ofSym symSwap).ne_iff.mpr apart)
      apply Or.inl
      dsimp [KRKNineNearStrip.RookCondition,Frame.ofSym,symSwap,dInf,absDiff] at *
      omega
  · refine swap_diagonal_entry distinct guard ((Frame.ofSym symSwap).ne_iff.mpr apart) ?_ (by decide) ?_
    · dsimp [symSwap,dInf,absDiff]; omega
    · apply KRKEightDiagonalEntries.second_region
      have notCheck := guard.2.2.2
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy] at notCheck
      dsimp [KRKSevenSecond.RookRegion,KRKNineNearStrip.RookCondition,symSwap] at *
      omega
  · refine KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) ?_ apart (by decide) ?_
    · dsimp [dInf,absDiff]; omega
    · apply KRKEightDiagonalEntries.near_region apart
      apply Or.inl
      dsimp [KRKNineNearStrip.RookCondition,dInf,absDiff] at *
      omega
  · apply (KRKNineNearStrip.clear_iff distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
      guard.2.1.symm guard.2.2.1 guard.2.2.2).mpr
    exact Or.inr ⟨Prod.ext (Fin.ext sx) (Fin.ext sy),rook⟩

theorem high_extra_clear {sk rs : Square} (region : HighExtra sk rs) : KRKTenGeometry.Clear sk rs (1,1) := by
  obtain ⟨sx,sy,ry,width⟩ := region
  have distinct : sk ≠ rs := by simp only [ne_iff_coords,sy,ry]; (try dsimp); omega
  have farR : 3 ≤ dInf rs (0,0) := by dsimp [dInf,absDiff]; omega
  have apart := corner_apart farR
  refine ⟨Or.inl ?_,⟨((1 : Fin 8),0),?_⟩,?_⟩
  · dsimp [dInf,absDiff]; omega
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry]
    simp <;> omega
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨
        t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨ t = ((1 : Fin 8),2) := by
      have distance := guard.1
      have separate := guard.2.2.1
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp [dInf,absDiff] at distance separate
      dsimp
      omega
    rcases targets with rfl | rfl | rfl | rfl | rfl | rfl
    · apply KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) ?_ apart (by decide)
        (KRKEightDiagonalEntries.corner_region farR)
      dsimp [dInf,absDiff]; omega
    · refine swap_diagonal_entry distinct guard ((Frame.ofSym symSwap).ne_iff.mpr apart) ?_ (by decide) ?_
      · dsimp [symSwap,dInf,absDiff]; omega
      · apply KRKEightDiagonalEntries.near_region ((Frame.ofSym symSwap).ne_iff.mpr apart)
        apply Or.inl
        dsimp [Frame.ofSym,symSwap,dInf,absDiff]; omega
    · refine swap_diagonal_entry distinct guard ((Frame.ofSym symSwap).ne_iff.mpr apart) ?_ (by decide) ?_
      · dsimp [symSwap,dInf,absDiff]; omega
      · exact KRKEightDiagonalEntries.second_region (Or.inl width)
    · refine KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) ?_ apart (by decide) ?_
      · dsimp [dInf,absDiff]; omega
      · apply KRKEightDiagonalEntries.near_region apart
        apply Or.inl
        dsimp [dInf,absDiff]; omega
    · refine KRKNineGeometry.king_step_clear (ns := ((2 : Fin 8),2)) ?_ apart (by decide) ?_
      · dsimp [dInf,absDiff]; omega
      · exact KRKEightDiagonalEntries.second_region (Or.inl (by omega))
    · apply (KRKNineNearStrip.clear_iff distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
        guard.2.1.symm guard.2.2.1 guard.2.2.2).mpr
      exact Or.inl ⟨ry,width,by dsimp [dInf,absDiff]; omega⟩

private theorem from_eight {sk rs : Square} (distinct : sk ≠ rs) (eight : KRKEightGeometry.Clear sk rs (1,1)) :
    KRKTenGeometry.Clear sk rs (1,1) := by
  refine ⟨eight.1,eight.2.1,?_⟩
  intro t guard
  let q := krkPos .white sk rs t .white
  have material : IsKRK q .white sk rs t :=
    ⟨distinct,ne_of_dInf_pos (by have h := guard.2.2.1; omega),guard.2.1.symm,rfl⟩
  have seven := (KRKSevenGeometry.kernel_seven_iff material rfl guard.2.2.1 guard.2.2.2).mpr (eight.2.2 _ guard)
  exact (KRKNineGeometry.kernel_nine_iff material rfl guard.2.2.1 guard.2.2.2).mp (mateWithin_mono seven (by decide))

private theorem horizontal_distinct {sk rs : Square} (region : Horizontal sk rs) : sk ≠ rs := by
  dsimp [Horizontal,SideExtra,HighExtra,KRKEightInner.Horizontal,KRKNineNearStrip.RookCondition] at region
  simp only [ne_iff_coords]
  omega

theorem horizontal_clear {sk rs : Square} (region : Horizontal sk rs) : KRKTenGeometry.Clear sk rs (1,1) := by
  have distinct := horizontal_distinct region
  rcases region with old | side | high
  · exact from_eight distinct (KRKEightInner.sufficient (Or.inl old))
  · exact side_extra_clear side
  · exact high_extra_clear high

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTenGeometry.Clear sk rs (1,1) := by
  rcases region with horizontal | vertical
  · exact horizontal_clear horizontal
  · have mapped := horizontal_clear vertical
    have back := KRKTenGeometry.frame_map (Frame.ofSym symSwap) (horizontal_distinct vertical) mapped
    simpa only [Frame.ofSym,symSwap.invol,show symSwap.f ((1 : Fin 8),1) = ((1 : Fin 8),1) from rfl] using back

theorem clear_iff {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,1)) :
    KRKTenGeometry.Clear sk rs (1,1) ↔ Region sk rs := ⟨necessary distinct far,sufficient⟩

theorem kernel_ten_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1)) :
    MateWithin σ 10 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTenGeometry.kernel_ten_iff material turn notMate).trans (clear_iff material.1 far)

theorem kernel_exact_ten {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1)) :
    (MateWithin σ 10 q ∧ ¬MateWithin σ 9 q) ↔ Region sk rs ∧ ¬KRKEightInner.Region sk rs := by
  constructor
  · rintro ⟨ten,notNine⟩
    refine ⟨(kernel_ten_iff material turn far).mp ten,?_⟩
    intro old
    exact notNine (mateWithin_mono ((KRKEightInner.kernel_eight_iff material turn far).mpr old) (by decide))
  · rintro ⟨region,notOld⟩
    refine ⟨(kernel_ten_iff material turn far).mpr region,?_⟩
    intro nine
    exact notOld ((KRKEightInner.kernel_eight_iff material turn far).mp (KRKEightGeometry.weak_nine_eight material turn nine))

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),1))
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKTenGeometry.Clear sk rs wk ↔ Region (g.f sk) (g.f rs) := by
  have mappedFar : 2 ≤ dInf (g.f sk) (1,1) := by rw [←target,g.distance]; exact far
  constructor
  · intro clear
    have mapped := KRKTenGeometry.frame_map g distinct clear
    rw [target] at mapped
    exact necessary (g.ne_iff.mpr distinct) mappedFar mapped
  · intro region
    have mapped := sufficient region
    rw [←target] at mapped
    have back := KRKTenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct) mapped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKTenInner
