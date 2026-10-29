import EndgameChess.Rules.KRKTwelveNearExact

namespace EndgameChess.Rules.KRKTwelveInner
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- A necessary coordinate reduction for a legal upper near-strip reply.
It is not yet a winning-region criterion. -/
def HorizontalPrison (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ 1 ≤ sk.2.val ∧ sk.2.val ≤ 3) ∨
  (sk.1.val = 4 ∧ 1 ≤ sk.2.val ∧ sk.2.val ≤ 3 ∧ rs.1.val = 2 ∧ rs.2.val = 3) ∨
  ((sk.2.val = 4 ∨ sk.2.val = 5) ∧ sk.1.val ≤ 2 ∧ rs.1.val = 2 ∧ 3 ≤ rs.2.val)

theorem near_guard_prison {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKTwelveGeometry.Clear sk rs (1,1)) (guard : KRKCornerWeakBand.Guard sk rs (1,1) (1,2)) :
    HorizontalPrison sk rs := by
  have evaluated := (KRKElevenNearStrip.clear_iff apart guard.2.1.symm).mp (clear.2.2 _ guard)
  have covered := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered apart clear (t := (2,2))
    (by decide) (Or.inl (by decide)))
  have safe := clear.1
  have nearFar := guard.2.2.1
  dsimp [SafeRook,dInf,absDiff] at safe far nearFar
  dsimp at covered
  rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
  · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,dInf,absDiff] at distance shape <;>
      dsimp [HorizontalPrison] <;> omega
  · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;>
      dsimp [KRKElevenNearStrip.RookCondition,KRKElevenNearStrip.SideRow,KRKElevenNearStrip.SideFile] at condition <;>
      dsimp at equal <;> dsimp [HorizontalPrison] <;> omega

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

def Prison (sk rs : Square) : Prop :=
  HorizontalPrison sk rs ∨ HorizontalPrison (symSwap.f sk) (symSwap.f rs) ∨ CornerPrison sk rs

theorem prison {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKTwelveGeometry.Clear sk rs (1,1)) : Prison sk rs := by
  by_cases near : KRKCornerWeakBand.Guard sk rs (1,1) (1,2)
  · exact Or.inl (near_guard_prison apart far clear near)
  have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symSwap) apart clear
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
    exact Or.inr (Or.inl (near_guard_prison (symSwap.ne_iff.mpr apart) mappedFar mapped actual))
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
    · exact KRKTwelveSecondCorner.bad_neighbour_covered apart clear (by decide) (Or.inl (by decide))
  exact Or.inr (Or.inr (corner_prison rfl rfl far clear.1 cover))

theorem same_file_rook_below {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 2)
    (sy : sk.2.val = 4 ∨ sk.2.val = 5) (rx : rs.1.val = 2)
    (clear : KRKTwelveGeometry.Clear sk rs (1,1)) : rs.2.val < sk.2.val := by
  by_cases below : rs.2.val < sk.2.val
  · exact below
  have notEqual : rs.2.val ≠ sk.2.val := by simp only [ne_iff_coords] at apart; omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,1) (2,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,rx]
    simp <;> omega
  have shallow := KRKTwelveGeometry.eleven_weak_depth (clear.2.2 _ guard)
  change 2 ≤ 1 at shallow
  contradiction

theorem zero_five_high_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 0)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) (high : 4 ≤ rs.2.val) :
    ¬KRKTwelveGeometry.Clear sk rs (1,1) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,1) (0,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((0 : Fin 8),2) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have equal : g.f sk = ((5 : Fin 8),0) := Prod.ext (Fin.ext sy) (Fin.ext sx)
  rw [equal] at mapped
  exact KRKElevenEdgeBoundary.second_five_zero_not_eleven high rx mapped

theorem one_five_high_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 1)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) (high : 5 ≤ rs.2.val) :
    ¬KRKTwelveGeometry.Clear sk rs (1,1) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,1) (0,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((0 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have equal : g.f sk = ((5 : Fin 8),1) := Prod.ext (Fin.ext sy) (Fin.ext sx)
  rw [equal] at mapped
  exact KRKElevenEdgeBoundary.near_five_one_not_eleven high rx mapped

def HorizontalSharp (sk rs : Square) : Prop :=
  HorizontalPrison sk rs ∧
    ((sk.1.val = 2 ∧ (sk.2.val = 4 ∨ sk.2.val = 5)) → rs.2.val < sk.2.val) ∧
    ((sk.1.val = 0 ∧ sk.2.val = 5) → rs.2.val = 3) ∧
    ((sk.1.val = 1 ∧ sk.2.val = 5) → rs.2.val ≤ 4)

theorem near_guard_sharp {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKTwelveGeometry.Clear sk rs (1,1)) (guard : KRKCornerWeakBand.Guard sk rs (1,1) (1,2)) :
    HorizontalSharp sk rs := by
  have shape := near_guard_prison apart far clear guard
  refine ⟨shape,?_,?_,?_⟩
  · rintro ⟨sx,sy⟩
    have rx : rs.1.val = 2 := by dsimp [HorizontalPrison] at shape; omega
    exact same_file_rook_below apart sx sy rx clear
  · rintro ⟨sx,sy⟩
    have data : rs.1.val = 2 ∧ 3 ≤ rs.2.val := by dsimp [HorizontalPrison] at shape; omega
    have notHigh : ¬4 ≤ rs.2.val := fun high => zero_five_high_no_clear apart sx sy data.1 high clear
    omega
  · rintro ⟨sx,sy⟩
    have data : rs.1.val = 2 ∧ 3 ≤ rs.2.val := by dsimp [HorizontalPrison] at shape; omega
    have notHigh : ¬5 ≤ rs.2.val := fun high => one_five_high_no_clear apart sx sy data.1 high clear
    omega

theorem ten_clear_subset {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKTenGeometry.Clear sk rs (1,1)) : KRKTwelveGeometry.Clear sk rs (1,1) := by
  have notRook : rs ≠ ((1 : Fin 8),1) := by
    intro equal
    have safe := clear.1
    rw [equal] at safe
    dsimp [SafeRook,dInf,absDiff] at safe far
    omega
  let q := krkPos .white sk rs (1,1) .black
  have material : IsKRK q .white sk rs (1,1) := ⟨apart,ne_of_dInf_pos (by omega),notRook,rfl⟩
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material rfl far).mp mate)
    change 1 = 0 at zero
    contradiction
  have ten := (KRKTenGeometry.kernel_ten_iff material rfl notMate).mpr clear
  exact (KRKTwelveGeometry.kernel_twelve_iff material rfl notMate).mp (mateWithin_mono ten (by decide))

end EndgameChess.Rules.KRKTwelveInner
