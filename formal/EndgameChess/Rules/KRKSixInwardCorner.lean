import EndgameChess.Rules.KRKFiveNear
import EndgameChess.Rules.KRKSixInterior

namespace EndgameChess.Rules.KRKSixInwardCorner
open EndgameChess.KK KRKFourPlyEscape
set_option maxHeartbeats 500000

def Region (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ sk.2.val = 1 ∧ rs.2.val = 2 ∧ 3 ≤ rs.1.val) ∨
  (sk.1.val = 1 ∧ sk.2.val = 3 ∧ rs.1.val = 2 ∧ 3 ≤ rs.2.val)

theorem near_from_step {sk rs wk u : Square} (distinct : sk ≠ rs)
    (every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKFiveGeometry.Clear sk rs t)
    (step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩) (rank : u.2.val = 0) (file : u.1.val = 1) :
    KRKFiveNear.Five sk rs := by
  have clear := every u step
  cases step with
  | lone distance notRook far notCheck =>
    exact (KRKFiveNear.clear_iff rank file distinct notRook.symm notCheck).mp clear

theorem horizontal_necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 1) (sx : sk.1.val = 3)
    (sy : sk.2.val ≤ 2) (ry : rs.2.val = 2) (safe : SafeRook sk rs wk)
    (every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKFiveGeometry.Clear sk rs t) :
    sk.2.val = 1 ∧ 3 ≤ rs.1.val := by
  have rx : 2 ≤ rs.1.val := by simp only [SafeRook,dInf,absDiff,file,rank,sx,ry] at safe; omega
  have south : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,((1 : Fin 8),0),true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,file,rank,sx,ry] <;> omega
  have five := near_from_step distinct every south rfl rfl
  simp [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,dInf,absDiff,sx,ry] at five
  simp only [square_eq_iff,Fin.ext_iff] at five
  (try dsimp only at five)
  have syLow : 1 ≤ sk.2.val ∧ 3 ≤ rs.1.val := by omega
  have notTwo : sk.2.val ≠ 2 := by
    intro two
    have upper : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,((2 : Fin 8),0),true⟩ := by
      simp only [ne_iff_coords] at distinct
      refine StepM.lone ?_ ?_ ?_ ?_ <;>
        simp only [dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,file,rank,sx,ry,two] <;> omega
    have clear := every _ upper
    have notRook : rs ≠ ((2 : Fin 8),0) := by rw [ne_iff_coords]; (try dsimp only); omega
    have notKing : sk ≠ ((2 : Fin 8),0) := by rw [ne_iff_coords]; (try dsimp only); omega
    have far : 2 ≤ dInf sk ((2 : Fin 8),0) := by simp only [dInf,absDiff,sx,two]; omega
    have notCheck : ¬RookSees rs ((2 : Fin 8),0) sk ((2 : Fin 8),0) := by
      simp only [RookSees,RookLine,OnSeg]; omega
    have bottom := (KRKFiveMiddle.bottom_clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide) (by decide)
      distinct notKing notRook far notCheck).mp clear
    have files := (KRKFiveMiddle.rank_two_bottom_iff (wk := ((2 : Fin 8),0)) (by decide) (by decide) two ry).mp bottom
    dsimp [KRKFiveMiddle.RankTwoFive] at files
    omega
  exact ⟨by omega,syLow.2⟩

theorem upper_escape {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 1) (sx : sk.1.val = 3)
    (rx : rs.1.val = 1) (ry : 3 ≤ rs.2.val)
    (every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKFiveGeometry.Clear sk rs t) : False := by
  let u : Square := (0,2)
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [u,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,file,rank,sx,rx] <;> omega
  have notRook : rs ≠ u := by rw [ne_iff_coords]; dsimp [u]; omega
  have notKing : sk ≠ u := by rw [ne_iff_coords]; dsimp [u]; omega
  have far : 2 ≤ dInf sk u := by simp only [u,dInf,absDiff,sx]; omega
  have notCheck : ¬RookSees rs u sk u := by simp only [u,RookSees,RookLine,OnSeg]; omega
  have swapped := KRKFiveGeometry.map symSwap distinct notKing notRook far notCheck (every u step)
  have mappedCheck : ¬RookSees (symSwap.f rs) (symSwap.f u) (symSwap.f sk) (symSwap.f u) :=
    fun seen => notCheck ((symSwap.sees_iff _ _ _ _).mp seen)
  have bottom := (KRKFiveMiddle.bottom_clear_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f u)
    rfl (by decide) (by decide) (symSwap.ne_iff.mpr distinct) (symSwap.ne_iff.mpr notKing)
    (symSwap.ne_iff.mpr notRook) (by rwa [symSwap.dInf_eq]) mappedCheck).mp swapped
  have forced := (KRKFiveMiddle.low_rook_bottom_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f u)
    (by decide) (by decide) (by dsimp [symSwap]; omega)).mp bottom
  have bad := forced.1
  dsimp [symSwap] at bad
  omega

theorem no_five_diagonal : ¬KRKFiveGeometry.Clear ((3 : Fin 8),3) ((2 : Fin 8),2) ((0 : Fin 8),0) := by
  intro clear
  simp only [KRKFiveGeometry.Clear,KRKFiveGeometry.KingPoints,KRKFiveGeometry.RookRays,
    KRKFiveMiddle.normalize_f (wk := ((0 : Fin 8),0)) (by rfl) (by decide),KRKFiveMiddle.normalize_r (wk := ((0 : Fin 8),0)) (by rfl) (by decide)] at clear
  rcases clear with immediate | ⟨_,⟨i,valid,region,distance,_⟩ | ⟨i,valid,equal,_⟩⟩
  · simp [KRKImmediate.MateNow,KRKMateGeometry.Horizontal,KRKImmediate.rankTarget,KRKImmediate.fileTarget] at immediate <;> omega
  · cases i <;> dsimp [KRKFourSlots.Valid,KRKFourSlots.Region,KRKFourSlots.king,KRKFourSlots.small] at valid region distance <;>
      dsimp [dInf,absDiff] at distance <;> omega
  · cases i <;> dsimp [KRKFourSlots.Valid,KRKFourSlots.king,KRKFourSlots.small] at valid equal <;>
      simp only [square_eq_iff] at equal <;> (try dsimp only at equal) <;> omega

theorem necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 1) (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKFiveGeometry.Clear sk rs t) : Region sk rs := by
  have cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t :=
    fun t distance inside => KRKCastleSix.interior_covered safe distance inside every
  rcases corner_prison file rank far safe cover with
    ⟨sx,sy,ry⟩ | ⟨sy,sx,rx⟩ | ⟨sx,sy,rx⟩ | ⟨sy,sx,ry⟩ | ⟨sx,sy,rx,ry⟩
  · have result := horizontal_necessary distinct file rank sx sy ry safe every
    exact Or.inl ⟨sx,result.1,ry,result.2⟩
  · have swappedSafe : SafeRook (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) := by
      simpa only [SafeRook,symSwap.dInf_eq] using safe
    have result := horizontal_necessary (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk)
      (symSwap.ne_iff.mpr distinct) rank file sy sx rx swappedSafe (KRKSixInterior.every_map symSwap distinct every)
    exact Or.inr ⟨result.1,sy,rx,result.2⟩
  · have height : 3 ≤ rs.2.val := by
      simp only [SafeRook,dInf,absDiff,file,rank,sx,rx] at safe
      omega
    exact False.elim (upper_escape distinct file rank sx rx height every)
  · have swappedSafe : SafeRook (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) := by
      simpa only [SafeRook,symSwap.dInf_eq] using safe
    have height : 3 ≤ rs.1.val := by
      simp only [SafeRook,dInf,absDiff,file,rank,sy,ry] at safe
      omega
    exact False.elim (upper_escape (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk)
      (symSwap.ne_iff.mpr distinct) rank file sy ry height (KRKSixInterior.every_map symSwap distinct every))
  · have kg : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rg : rs = ((2 : Fin 8),2) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,((0 : Fin 8),0),true⟩ := by
      refine StepM.lone ?_ ?_ ?_ ?_ <;>
        simp only [dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,file,rank,sx,sy,rx,ry] <;> omega
    have five := every _ step
    rw [kg,rg] at five
    exact False.elim (no_five_diagonal five)


theorem horizontal_replies {sk rs wk : Square} (file : wk.1.val = 1) (rank : wk.2.val = 1)
    (sx : sk.1.val = 3) (sy : sk.2.val = 1) (ry : rs.2.val = 2) (rx : 3 ≤ rs.1.val) :
    ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKFiveGeometry.Clear sk rs t := by
  intro t step
  cases step with
  | lone distance notRook far notCheck =>
    have choices : (t.1.val = 0 ∧ t.2.val = 0) ∨ (t.1.val = 0 ∧ t.2.val = 1) ∨
        (t.1.val = 1 ∧ t.2.val = 0) := by
      simp only [dInf,absDiff,file,rank,sx,sy] at distance far
      simp only [RookSees,RookLine,OnSeg,sx,sy,ry] at notCheck
      omega
    have distinct : sk ≠ rs := by rw [ne_iff_coords]; omega
    have notKing : sk ≠ t := ne_of_dInf_pos (by omega)
    rcases choices with ⟨tx,ty⟩ | ⟨tx,ty⟩ | ⟨tx,ty⟩
    · refine Or.inr ⟨by simp only [KRKEdgeDepth.depth,tx,ty]; omega,Or.inl ?_⟩
      simp only [KRKFiveGeometry.KingPoints,KRKFiveMiddle.normalize_f ty (by omega),KRKFiveMiddle.normalize_r ty (by omega)]
      refine ⟨.c21,tx,by change 1 ≤ rs.1.val; omega,?_,?_,?_,?_,?_⟩
      · simp only [KRKFourSlots.king,dInf,absDiff,sx,sy]; omega
      · simp only [KRKFourSlots.king,ne_iff_coords]; (try dsimp only); omega
      · simp only [KRKFourSlots.king,dInf,absDiff,tx,ty]; omega
      · refine ⟨((0 : Fin 8),1),?_⟩
        dsimp [KRKFiveGeometry.Live,KRKFourSlots.king] at *
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,tx,ty]
        omega
      · apply Or.inl
        simp only [dInf,absDiff,tx,ty]; omega
    · have swapped : KRKFiveGeometry.Clear (symSwap.f sk) (symSwap.f rs) (symSwap.f t) := by
        apply (KRKFiveNear.clear_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f t)
          tx ty (symSwap.ne_iff.mpr distinct) (symSwap.ne_iff.mpr notRook.symm)
          (fun seen => notCheck ((symSwap.sees_iff _ _ _ _).mp seen))).mpr
        left
        right
        left
        refine ⟨Or.inl ?_,?_⟩
        · change 3 ≤ rs.1.val; exact rx
        · dsimp [symSwap,dInf,absDiff]; omega
      exact (KRKFiveGeometry.map_iff symSwap distinct notKing notRook.symm far notCheck).mp swapped
    · apply (KRKFiveNear.clear_iff ty tx distinct notRook.symm notCheck).mpr
      left
      right
      right
      refine ⟨Or.inr ⟨rx,?_⟩,?_⟩
      · change ¬(rs.1.val = 3 ∧ rs.2.val = 1); omega
      · simp only [dInf,absDiff,sx,sy]; omega

theorem replies_of_region {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 1) (region : Region sk rs) :
    ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKFiveGeometry.Clear sk rs t := by
  rcases region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩
  · exact horizontal_replies file rank sx sy ry rx
  · intro t step
    have swapped := horizontal_replies (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk)
      rank file sy sx rx ry (symSwap.f t) (step_map symSwap step)
    have far : 2 ≤ dInf sk t := by cases step with | lone _ _ h _ => exact h
    have notRook : rs ≠ t := by cases step with | lone _ h _ _ => exact h.symm
    have notCheck : ¬RookSees rs t sk t := by cases step with | lone _ _ _ h => exact h
    exact (KRKFiveGeometry.map_iff symSwap distinct (ne_of_dInf_pos (by omega)) notRook far notCheck).mp swapped

theorem kernel_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (file : wk.1.val = 1) (rank : wk.2.val = 1) : MateWithin σ 6 q ↔ Region sk rs := by
  have inside : 0 < KRKEdgeDepth.depth wk := by simp only [KRKEdgeDepth.depth,file,rank]; omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  rw [KRKSixGeometry.kernel_six_iff material turn notMate]
  constructor
  · intro geometry
    exact necessary material.1 file rank far geometry.1
      (fun t step => geometry.2.2 t (KRKCornerWeakBand.step_guard step))
  · intro region
    have safe : SafeRook sk rs wk := by
      rcases region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩ <;>
        apply Or.inl <;> simp only [dInf,absDiff,file,rank] <;> omega
    have live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t := by
      refine ⟨((0 : Fin 8),0),?_⟩
      rcases region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩ <;>
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,file,rank] <;> omega
    refine ⟨safe,live,?_⟩
    intro t guard
    exact replies_of_region material.1 file rank region t (StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2)


theorem region_clear {sk rs wk : Square} (distinct : sk ≠ rs) (file : wk.1.val = 1) (rank : wk.2.val = 1)
    (region : Region sk rs) : KRKSixGeometry.Clear sk rs wk := by
  have safe : SafeRook sk rs wk := by
    rcases region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩ <;>
      apply Or.inl <;> simp only [dInf,absDiff,file,rank] <;> omega
  have live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t := by
    refine ⟨((0 : Fin 8),0),?_⟩
    rcases region with ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩ <;>
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,file,rank] <;> omega
  refine ⟨safe,live,?_⟩
  intro t guard
  exact replies_of_region distinct file rank region t (StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2)

theorem map_six (g : BoardSym) {sk rs wk : Square} (distinct : sk ≠ rs) (clear : KRKSixGeometry.Clear sk rs wk) :
    KRKSixGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by
  obtain ⟨safe,⟨t,guard⟩,all⟩ := clear
  have mappedSafe : SafeRook (g.f sk) (g.f rs) (g.f wk) := by simpa only [SafeRook,g.dInf_eq] using safe
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2
  have every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u :=
    fun u step => all u (KRKCornerWeakBand.step_guard step)
  refine ⟨mappedSafe,⟨g.f t,KRKCornerWeakBand.step_guard (step_map g step)⟩,?_⟩
  intro u guard
  exact KRKSixInterior.every_map g distinct every u (StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2)

def innerSym (wk : Square) : BoardSym :=
  if wk.1.val = 1 then (if wk.2.val = 1 then symId else symY)
  else (if wk.2.val = 1 then symX else symXY)

theorem inner_sym_spec {wk : Square} (inner : KRKSixInterior.InnerCorner wk) :
    (innerSym wk).f wk = ((1 : Fin 8),1) := by
  by_cases x : wk.1.val = 1 <;> by_cases y : wk.2.val = 1 <;>
    simp only [innerSym,x,y,↓reduceIte] <;>
    rw [square_eq_iff] <;> dsimp [symId,symX,symY,symXY] <;> dsimp [KRKSixInterior.InnerCorner] at inner <;> omega

def GlobalRegion (sk rs wk : Square) : Prop :=
  KRKSixInterior.InnerCorner wk ∧ Region ((innerSym wk).f sk) ((innerSym wk).f rs)

/-- Exact six-ply kernel criterion over the entire interior, all four
inward corners included. Only coordinates are reflected. -/
theorem global_kernel_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (inside : 0 < KRKEdgeDepth.depth wk) : MateWithin σ 6 q ↔ GlobalRegion sk rs wk := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  rw [KRKSixGeometry.kernel_six_iff material turn notMate]
  constructor
  · intro clear
    have inner := KRKSixInterior.interior_corner_necessary material.1 inside far clear.1
      (fun t step => clear.2.2 t (KRKCornerWeakBand.step_guard step))
    have mapped := map_six (innerSym wk) material.1 clear
    have spec := inner_sym_spec inner
    have region := necessary (wk := (innerSym wk).f wk) ((innerSym wk).ne_iff.mpr material.1)
      (by rw [spec]; rfl) (by rw [spec]; rfl) (by rwa [(innerSym wk).dInf_eq]) mapped.1
      (fun t step => mapped.2.2 t (KRKCornerWeakBand.step_guard step))
    exact ⟨inner,region⟩
  · rintro ⟨inner,region⟩
    have spec := inner_sym_spec inner
    have mapped := region_clear (wk := (innerSym wk).f wk) ((innerSym wk).ne_iff.mpr material.1)
      (by rw [spec]; rfl) (by rw [spec]; rfl) region
    simpa only [(innerSym wk).invol] using map_six (innerSym wk) ((innerSym wk).ne_iff.mpr material.1) mapped

theorem global_kernel_exact_six {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (inside : 0 < KRKEdgeDepth.depth wk) (region : GlobalRegion sk rs wk) :
    MateWithin σ 6 q ∧ ¬MateWithin σ 5 q :=
  ⟨(global_kernel_six_iff material turn far inside).mpr region,
    KRKFourPlyEscape.weak_interior_not_five material turn far inside⟩

end EndgameChess.Rules.KRKSixInwardCorner
