import EndgameChess.Rules.KRKTwelveNearNewEntries

namespace EndgameChess.Rules.KRKTwelveNearUpper
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

def Region (sk rs : Square) : Prop :=
  sk.2.val = 4 ∧ rs.1.val = 2 ∧
    ((sk.1.val = 0 ∧ 4 ≤ rs.2.val) ∨ (sk.1.val = 1 ∧ 3 ≤ rs.2.val) ∨
      (sk.1.val = 2 ∧ rs.2.val = 3))

theorem blocked_high_no_clear {sk rs : Square} (sx : sk.1.val = 2) (sy : sk.2.val = 4)
    (rx : rs.1.val = 2) (high : 5 ≤ rs.2.val) : ¬KRKTwelveGeometry.Clear sk rs (1,2) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (2,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  have shallow := KRKTwelveGeometry.eleven_weak_depth (clear.2.2 _ guard)
  change 2 ≤ 1 at shallow
  contradiction

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (sy : sk.2.val = 4)
    (sx : sk.1.val ≤ 2) (rx : rs.1.val = 2) (clear : KRKTwelveGeometry.Clear sk rs (1,2)) : Region sk rs := by
  have safe := clear.1
  have height : rs.2.val = 0 ∨ 3 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
  have notZero : rs.2.val ≠ 0 := fun row => KRKTwelveNearStrip.upper_low_no_clear apart sy sx rx row clear
  have tall : 3 ≤ rs.2.val := height.resolve_left notZero
  have files : sk.1.val = 0 ∨ sk.1.val = 1 ∨ sk.1.val = 2 := by omega
  refine ⟨sy,rx,?_⟩
  rcases files with zero | one | two
  · refine Or.inl ⟨zero,?_⟩
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  · exact Or.inr (Or.inl ⟨one,tall⟩)
  · have notFour : rs.2.val ≠ 4 := by simp only [ne_iff_coords] at apart; omega
    have notHigh : ¬5 ≤ rs.2.val := fun high => blocked_high_no_clear two sy rx high clear
    exact Or.inr (Or.inr ⟨two,by omega⟩)

/-- Monotonicity of the already evaluated ten-ply board certificate. -/
theorem ten_clear_subset {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKTenGeometry.Clear sk rs (1,2)) : KRKTwelveGeometry.Clear sk rs (1,2) := by
  have notRook : rs ≠ ((1 : Fin 8),2) := by
    intro equal
    have safe := clear.1
    rw [equal] at safe
    dsimp [SafeRook,dInf,absDiff] at safe far
    omega
  let q := krkPos .white sk rs (1,2) .black
  have material : IsKRK q .white sk rs (1,2) := ⟨apart,ne_of_dInf_pos (by omega),notRook,rfl⟩
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material rfl far).mp mate)
    change 1 = 0 at zero
    contradiction
  have ten := (KRKTenGeometry.kernel_ten_iff material rfl notMate).mpr clear
  exact (KRKTwelveGeometry.kernel_twelve_iff material rfl notMate).mp (mateWithin_mono ten (by decide))

theorem protected_clear : KRKTwelveGeometry.Clear ((2 : Fin 8),4) ((2 : Fin 8),3) (1,2) := by
  refine ⟨Or.inr (by decide),⟨((0 : Fin 8),1),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
    decide
  · intro t guard
    have targets : t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, j = 1 ∨ j = 2 →
        KRKCornerWeakBand.Guard ((2 : Fin 8),4) ((2 : Fin 8),3) (1,2) (0,j) →
        KRKElevenGeometry.Clear ((2 : Fin 8),4) ((2 : Fin 8),3) (0,j) := by
      intro j choice guard
      let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f ((2 : Fin 8),4)) (g.f ((2 : Fin 8),3)) (g.f ((0 : Fin 8),j)) :=
        KRKTwelveNearNewEntries.upper_low_eleven choice
      have back := KRKElevenGeometry.frame_map g.inverse (by decide)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl
    · exact edge (Or.inl rfl) guard
    · exact edge (Or.inr rfl) guard
    · exact KRKTwelveNearNewEntries.upper_inner_eleven

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTwelveGeometry.Clear sk rs (1,2) := by
  obtain ⟨sy,rx,⟨zero,height⟩ | ⟨one,height⟩ | ⟨two,row⟩⟩ := region
  · have old : KRKTenNearStrip.Upper sk rs := ⟨sy,rx,Or.inl ⟨zero,height⟩⟩
    have apart : sk ≠ rs := by simp only [ne_iff_coords,zero,rx]; omega
    apply ten_clear_subset apart ?_ (KRKTenNearStrip.upper_clear old)
    dsimp [dInf,absDiff]; omega
  · have old : KRKTenNearStrip.Upper sk rs := ⟨sy,rx,Or.inr ⟨one,height⟩⟩
    have apart : sk ≠ rs := by simp only [ne_iff_coords,one,rx]; omega
    apply ten_clear_subset apart ?_ (KRKTenNearStrip.upper_clear old)
    dsimp [dInf,absDiff]; omega
  · have kingEq : sk = ((2 : Fin 8),4) := Prod.ext (Fin.ext two) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),3) := Prod.ext (Fin.ext rx) (Fin.ext row)
    rw [kingEq,rookEq]
    exact protected_clear

end EndgameChess.Rules.KRKTwelveNearUpper
