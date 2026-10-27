import EndgameChess.Rules.KRKSixInwardCorner

namespace EndgameChess.Rules.KRKSixCorner
open EndgameChess.KK KRKFourPlyEscape KRKMateGeometry
set_option maxHeartbeats 300000

def Region (sk rs : Square) : Prop :=
  (sk.1.val = 0 ∧ sk.2.val = 2 ∧ (2 ≤ rs.2.val ∨ rs.1.val = 2 ∨ (rs.1.val = 3 ∧ rs.2.val = 1))) ∨
  (sk.1.val = 2 ∧ sk.2.val = 0 ∧ (2 ≤ rs.1.val ∨ rs.2.val = 2 ∨ (rs.1.val = 1 ∧ rs.2.val = 3))) ∨
  (sk.1.val = 1 ∧ sk.2.val = 2 ∧ 1 ≤ rs.2.val) ∨
  (sk.1.val = 2 ∧ sk.2.val = 1 ∧ 1 ≤ rs.1.val) ∨
  (sk.1.val = 2 ∧ sk.2.val = 2) ∨
  (sk.1.val = 0 ∧ sk.2.val = 3 ∧ rs.2.val = 1 ∧ (rs.1.val = 2 ∨ rs.1.val = 3)) ∨
  (sk.1.val = 3 ∧ sk.2.val = 0 ∧ rs.1.val = 1 ∧ (rs.2.val = 2 ∨ rs.2.val = 3)) ∨
  ((sk.1.val = 1 ∨ sk.1.val = 2) ∧ sk.2.val = 3 ∧
    ((rs.2.val = 1 ∧ 2 ≤ rs.1.val) ∨ (sk.1.val = 2 ∧ rs.1.val = 1 ∧ 4 ≤ rs.2.val))) ∨
  (sk.1.val = 3 ∧ (sk.2.val = 1 ∨ sk.2.val = 2) ∧
    ((rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨ (sk.2.val = 2 ∧ rs.2.val = 1 ∧ 4 ≤ rs.1.val))) ∨
  (sk.1.val = 3 ∧ sk.2.val = 3 ∧
    ((rs.1.val = 1 ∧ 4 ≤ rs.2.val) ∨ (rs.2.val = 1 ∧ 4 ≤ rs.1.val)))

theorem blocked_or_near {sk rs wk t : Square} (distinct : sk ≠ rs) (safe : SafeRook sk rs wk)
    (distance : dInf wk t = 1) (file : t.1.val = 1) (rank : t.2.val = 0)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) :
    dInf sk t ≤ 1 ∨ RookSees rs t sk t ∨ KRKFiveNear.Five sk rs := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases seen : RookSees rs t sk t
  · exact Or.inr (Or.inl seen)
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have far : 2 ≤ dInf sk t := by omega
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone distance notRook far seen
  exact Or.inr (Or.inr ((KRKFiveNear.clear_iff rank file distinct notRook.symm seen).mp (every t step)))

theorem live_not_diagonal_rook {sk rs wk : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t) : rs ≠ ((1 : Fin 8),1) := by
  rintro rfl
  obtain ⟨t,guard⟩ := live
  simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,file,rank] at far guard
  try dsimp only at far guard
  omega

private theorem val0 : ((0 : Fin 8).val) = 0 := rfl
private theorem val1 : ((1 : Fin 8).val) = 1 := rfl
private theorem val2 : ((2 : Fin 8).val) = 2 := rfl
private theorem val3 : ((3 : Fin 8).val) = 3 := rfl
private theorem val4 : ((4 : Fin 8).val) = 4 := rfl
private theorem val5 : ((5 : Fin 8).val) = 5 := rfl
private theorem val6 : ((6 : Fin 8).val) = 6 := rfl
private theorem val7 : ((7 : Fin 8).val) = 7 := rfl

private theorem arithmetic_x0 {sk rs : Square} (sx : sk.1.val = 0)
    (far : 2 ≤ max sk.1.val sk.2.val) (safe : SafeRook sk rs (0,0)) (distinct : sk ≠ rs) (notCenter : rs ≠ ((1 : Fin 8),1))
    (inward : dInf sk ((1 : Fin 8),1) ≤ 1 ∨ RookSees rs ((1 : Fin 8),1) sk ((1 : Fin 8),1))
    (south : dInf sk ((1 : Fin 8),0) ≤ 1 ∨ RookSees rs ((1 : Fin 8),0) sk ((1 : Fin 8),0) ∨ KRKFiveNear.Five sk rs)
    (west : dInf (symSwap.f sk) ((1 : Fin 8),0) ≤ 1 ∨ RookSees (symSwap.f rs) ((1 : Fin 8),0) (symSwap.f sk) ((1 : Fin 8),0) ∨ KRKFiveNear.Five (symSwap.f sk) (symSwap.f rs)) :
    Terminal sk rs (0,0) ∨ Region sk rs := by
  have syCases : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  by_cases rx : rs.1.val = 1 <;> by_cases ry : rs.2.val = 1 <;>
    rcases syCases with sy | sy | sy | sy | sy <;>
    simp_all only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,symSwap,
      RookSees,RookLine,OnSeg,dInf,absDiff,Region,Terminal,Horizontal,SafeRook,ne_iff_coords,square_eq_iff,Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] <;>
    (try dsimp only at *) <;> (try simp_all [val0,val1,val2,val3,val4,val5,val6,val7]) <;> (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] at *) <;> omega

private theorem arithmetic_x1 {sk rs : Square} (sx : sk.1.val = 1)
    (far : 2 ≤ max sk.1.val sk.2.val) (safe : SafeRook sk rs (0,0)) (distinct : sk ≠ rs) (notCenter : rs ≠ ((1 : Fin 8),1))
    (inward : dInf sk ((1 : Fin 8),1) ≤ 1 ∨ RookSees rs ((1 : Fin 8),1) sk ((1 : Fin 8),1))
    (south : dInf sk ((1 : Fin 8),0) ≤ 1 ∨ RookSees rs ((1 : Fin 8),0) sk ((1 : Fin 8),0) ∨ KRKFiveNear.Five sk rs)
    (west : dInf (symSwap.f sk) ((1 : Fin 8),0) ≤ 1 ∨ RookSees (symSwap.f rs) ((1 : Fin 8),0) (symSwap.f sk) ((1 : Fin 8),0) ∨ KRKFiveNear.Five (symSwap.f sk) (symSwap.f rs)) :
    Terminal sk rs (0,0) ∨ Region sk rs := by
  have syCases : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  by_cases rx : rs.1.val = 1 <;> by_cases ry : rs.2.val = 1 <;>
    rcases syCases with sy | sy | sy | sy | sy <;>
    simp_all only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,symSwap,
      RookSees,RookLine,OnSeg,dInf,absDiff,Region,Terminal,Horizontal,SafeRook,ne_iff_coords,square_eq_iff,Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] <;>
    (try dsimp only at *) <;> (try simp_all [val0,val1,val2,val3,val4,val5,val6,val7]) <;> (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] at *) <;> omega

private theorem arithmetic_x2 {sk rs : Square} (sx : sk.1.val = 2)
    (far : 2 ≤ max sk.1.val sk.2.val) (safe : SafeRook sk rs (0,0)) (distinct : sk ≠ rs) (notCenter : rs ≠ ((1 : Fin 8),1))
    (inward : dInf sk ((1 : Fin 8),1) ≤ 1 ∨ RookSees rs ((1 : Fin 8),1) sk ((1 : Fin 8),1))
    (south : dInf sk ((1 : Fin 8),0) ≤ 1 ∨ RookSees rs ((1 : Fin 8),0) sk ((1 : Fin 8),0) ∨ KRKFiveNear.Five sk rs)
    (west : dInf (symSwap.f sk) ((1 : Fin 8),0) ≤ 1 ∨ RookSees (symSwap.f rs) ((1 : Fin 8),0) (symSwap.f sk) ((1 : Fin 8),0) ∨ KRKFiveNear.Five (symSwap.f sk) (symSwap.f rs)) :
    Terminal sk rs (0,0) ∨ Region sk rs := by
  have syCases : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  by_cases rx : rs.1.val = 1 <;> by_cases ry : rs.2.val = 1 <;>
    rcases syCases with sy | sy | sy | sy | sy <;>
    simp_all only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,symSwap,
      RookSees,RookLine,OnSeg,dInf,absDiff,Region,Terminal,Horizontal,SafeRook,ne_iff_coords,square_eq_iff,Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] <;>
    (try dsimp only at *) <;> (try simp_all [val0,val1,val2,val3,val4,val5,val6,val7]) <;> (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] at *) <;> omega

private theorem arithmetic_x3 {sk rs : Square} (sx : sk.1.val = 3)
    (far : 2 ≤ max sk.1.val sk.2.val) (safe : SafeRook sk rs (0,0)) (distinct : sk ≠ rs) (notCenter : rs ≠ ((1 : Fin 8),1))
    (inward : dInf sk ((1 : Fin 8),1) ≤ 1 ∨ RookSees rs ((1 : Fin 8),1) sk ((1 : Fin 8),1))
    (south : dInf sk ((1 : Fin 8),0) ≤ 1 ∨ RookSees rs ((1 : Fin 8),0) sk ((1 : Fin 8),0) ∨ KRKFiveNear.Five sk rs)
    (west : dInf (symSwap.f sk) ((1 : Fin 8),0) ≤ 1 ∨ RookSees (symSwap.f rs) ((1 : Fin 8),0) (symSwap.f sk) ((1 : Fin 8),0) ∨ KRKFiveNear.Five (symSwap.f sk) (symSwap.f rs)) :
    Terminal sk rs (0,0) ∨ Region sk rs := by
  have syCases : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
  by_cases rx : rs.1.val = 1 <;> by_cases ry : rs.2.val = 1 <;>
    rcases syCases with sy | sy | sy | sy | sy <;>
    simp_all only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,symSwap,
      RookSees,RookLine,OnSeg,dInf,absDiff,Region,Terminal,Horizontal,SafeRook,ne_iff_coords,square_eq_iff,Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] <;>
    (try dsimp only at *) <;> (try simp_all [val0,val1,val2,val3,val4,val5,val6,val7]) <;> (try simp only [Fin.ext_iff,val0,val1,val2,val3,val4,val5,val6,val7] at *) <;> omega

private theorem arithmetic_x4 {sk rs : Square} (sx : 4 ≤ sk.1.val)
    (far : 2 ≤ max sk.1.val sk.2.val) (safe : SafeRook sk rs (0,0)) (distinct : sk ≠ rs) (notCenter : rs ≠ ((1 : Fin 8),1))
    (inward : dInf sk ((1 : Fin 8),1) ≤ 1 ∨ RookSees rs ((1 : Fin 8),1) sk ((1 : Fin 8),1))
    (south : dInf sk ((1 : Fin 8),0) ≤ 1 ∨ RookSees rs ((1 : Fin 8),0) sk ((1 : Fin 8),0) ∨ KRKFiveNear.Five sk rs)
    (west : dInf (symSwap.f sk) ((1 : Fin 8),0) ≤ 1 ∨ RookSees (symSwap.f rs) ((1 : Fin 8),0) (symSwap.f sk) ((1 : Fin 8),0) ∨ KRKFiveNear.Five (symSwap.f sk) (symSwap.f rs)) :
    Terminal sk rs (0,0) ∨ Region sk rs := by
  have notSouth : ¬KRKFiveNear.Five sk rs := by
    intro five
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2] at five
    omega
  have notWest : ¬KRKFiveNear.Five (symSwap.f sk) (symSwap.f rs) := by
    intro five
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      symSwap,dInf,absDiff,val0,val1,val2] at five
    omega
  have southLine : rs.1.val = 1 ∨ rs.2.val = 0 := by
    rcases south with close | seen | five
    · simp only [dInf,absDiff,val0,val1] at close; omega
    · exact seen.1.2
    · exact False.elim (notSouth five)
  have westLine : rs.2.val = 1 ∨ rs.1.val = 0 := by
    rcases west with close | seen | five
    · simp only [symSwap,dInf,absDiff,val0,val1] at close; omega
    · exact seen.1.2
    · exact False.elim (notWest five)
  have inwardLine : rs.1.val = 1 ∨ rs.2.val = 1 := by
    rcases inward with close | seen
    · simp only [dInf,absDiff,val1] at close; omega
    · exact seen.1.2
  clear south west inward notSouth notWest
  simp only [SafeRook,dInf,absDiff,val0] at safe
  omega


theorem corner_six_necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) :
    Terminal sk rs wk ∨ Region sk rs := by
  have inward : dInf sk ((1 : Fin 8),1) ≤ 1 ∨ RookSees rs ((1 : Fin 8),1) sk ((1 : Fin 8),1) := by
    by_cases close : dInf sk ((1 : Fin 8),1) ≤ 1
    · exact Or.inl close
    by_cases seen : RookSees rs ((1 : Fin 8),1) sk ((1 : Fin 8),1)
    · exact Or.inr seen
    have distance : dInf wk ((1 : Fin 8),1) = 1 := by simp [dInf,absDiff,file,rank]
    have apart : ((1 : Fin 8),1) ≠ rs := by
      intro equal
      rcases safe with distant | guarded
      · rw [←equal] at distant; simp [dInf,absDiff,file,rank] at distant
      · rw [←equal] at guarded; omega
    have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,((1 : Fin 8),1),true⟩ := StepM.lone distance apart (by omega) seen
    have zero := KRKCastleSix.five_depth_zero (every _ step)
    have positive : KRKEdgeDepth.depth ((1 : Fin 8),1) = 1 := by decide
    omega
  have south := blocked_or_near (t := ((1 : Fin 8),0)) distinct safe (by simp [dInf,absDiff,file,rank]) rfl rfl every
  have swappedSafe : SafeRook (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) := by
    simpa only [SafeRook,symSwap.dInf_eq] using safe
  have west := blocked_or_near (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk)
    (t := ((1 : Fin 8),0)) (symSwap.ne_iff.mpr distinct) swappedSafe
    (by simp [symSwap,dInf,absDiff,file,rank]) rfl rfl (KRKSixInterior.every_map symSwap distinct every)
  have notCenter := live_not_diagonal_rook file rank far live
  have root : wk = ((0 : Fin 8),0) := by rw [square_eq_iff]; exact ⟨file,rank⟩
  have distance : 2 ≤ max sk.1.val sk.2.val := by simpa [dInf,absDiff,file,rank] using far
  rw [root] at safe ⊢
  have sxCases : sk.1.val = 0 ∨ sk.1.val = 1 ∨ sk.1.val = 2 ∨ sk.1.val = 3 ∨ 4 ≤ sk.1.val := by omega
  rcases sxCases with sx | sx | sx | sx | sx
  · exact arithmetic_x0 sx distance safe distinct notCenter inward south west
  · exact arithmetic_x1 sx distance safe distinct notCenter inward south west
  · exact arithmetic_x2 sx distance safe distinct notCenter inward south west
  · exact arithmetic_x3 sx distance safe distinct notCenter inward south west
  · exact arithmetic_x4 sx distance safe distinct notCenter inward south west

private theorem region_swap_forward {sk rs : Square} (region : Region sk rs) :
    Region (symSwap.f sk) (symSwap.f rs) := by
  rcases region with h | h | h | h | h | h | h | h | h | h
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inl ?_)
    omega
  · dsimp [Region,symSwap]
    refine Or.inl ?_
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inl ?_))
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
    omega
  · dsimp [Region,symSwap]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))))
    omega

theorem region_swap {sk rs : Square} : Region (symSwap.f sk) (symSwap.f rs) ↔ Region sk rs := by
  constructor
  · intro h
    simpa only [symSwap] using region_swap_forward h
  · exact region_swap_forward

theorem region_excludes_inward {sk rs : Square} (region : Region sk rs) :
    ¬KRKCornerWeakBand.Guard sk rs (0,0) (1,1) := by
  intro guard
  simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
    val0,val1,val2] at guard
  rcases region with h | h | h | h | h | h | h | h | h | h <;> omega

theorem region_south_five {sk rs : Square} (region : Region sk rs)
    (guard : KRKCornerWeakBand.Guard sk rs (0,0) (1,0)) : KRKFiveNear.Five sk rs := by
  rcases region with h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega
  · rcases h with ⟨sx,sy,condition⟩
    simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,dInf,absDiff,ne_iff_coords,
      val0,val1,val2,sx,sy] at guard <;>
    simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,square_eq_iff,
      dInf,absDiff,val0,val1,val2,sx,sy] <;>
    (try dsimp only at *) <;>
    (try simp_all [val0,val1,val2]) <;>
    (try simp only [Fin.ext_iff,val0,val1,val2] at *) <;>
    omega

theorem region_replies {sk rs wk t : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) (region : Region sk rs)
    (step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩) : KRKFiveGeometry.Clear sk rs t := by
  have root : wk = ((0 : Fin 8),0) := by rw [square_eq_iff]; exact ⟨file,rank⟩
  have guard := KRKCornerWeakBand.step_guard step
  have neighbours := KRKCornerWeakBand.neighbour_cases file rank guard.1
  rw [root] at guard
  rcases neighbours with rfl | rfl | rfl
  · exact (KRKFiveNear.clear_iff rfl rfl distinct guard.2.1.symm guard.2.2.2).mpr (region_south_five region guard)
  · have mappedGuard : KRKCornerWeakBand.Guard (symSwap.f sk) (symSwap.f rs) (0,0) (1,0) := by
      have mapped := KRKCornerWeakBand.step_guard (step_map symSwap step)
      simpa only [root,KRKCornerWeakBand.north,symSwap] using mapped
    have clear := (KRKFiveNear.clear_iff rfl rfl (symSwap.ne_iff.mpr distinct)
      mappedGuard.2.1.symm mappedGuard.2.2.2).mpr (region_south_five (region_swap.mpr region) mappedGuard)
    apply (KRKFiveGeometry.map_iff symSwap distinct (ne_of_dInf_pos (by have := guard.2.2.1; omega))
      guard.2.1.symm guard.2.2.1 guard.2.2.2).mp
    simpa only [KRKCornerWeakBand.north,symSwap] using clear
  · exact False.elim (region_excludes_inward region guard)

theorem kernel_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) : MateWithin σ 6 q ↔
      Terminal sk rs wk ∨ (Region sk rs ∧ SafeRook sk rs wk ∧ ∃ t, KRKCornerWeakBand.Guard sk rs wk t) := by
  by_cases mate : MatedK q
  · have terminal := (KRKMateGeometry.kernel_mate_iff material turn far).mp mate
    exact ⟨fun _ => Or.inl terminal,fun _ => Or.inl ⟨turn,mate⟩⟩
  rw [KRKSixGeometry.kernel_six_iff material turn mate]
  constructor
  · rintro ⟨safe,live,every⟩
    have necessary := corner_six_necessary material.1 file rank far safe live
      (fun t step => every t (KRKCornerWeakBand.step_guard step))
    exact necessary.elim Or.inl (fun region => Or.inr ⟨region,safe,live⟩)
  · rintro (terminal | ⟨region,safe,live⟩)
    · exact False.elim (mate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal))
    · exact ⟨safe,live,fun t guard => region_replies material.1 file rank region
        (StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2)⟩

end EndgameChess.Rules.KRKSixCorner
