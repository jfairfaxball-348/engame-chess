import EndgameChess.Rules.KRKTwelveInnerSide

namespace EndgameChess.Rules.KRKTwelveInnerHigh
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem diagonal_edge_eight {rs : Square} (apart : ((2 : Fin 8),2) ≠ rs)
    (x : 2 ≤ rs.1.val) (y : 2 ≤ rs.2.val) {j : Fin 8} (edge : j = 0 ∨ j = 1 ∨ j = 2) :
    KRKEightGlobal.Region (2,2) rs (j,0) := by
  have spread : 3 ≤ rs.1.val ∨ 3 ≤ rs.2.val := by
    simp only [ne_iff_coords] at apart
    dsimp at apart
    omega
  rcases edge with rfl | rfl | rfl
  · apply KRKEightDiagonalEntries.corner_region
    dsimp [dInf,absDiff]; omega
  · exact KRKEightDiagonalEntries.near_region apart (Or.inl (by dsimp [dInf,absDiff]; omega))
  · apply KRKEightDiagonalEntries.second_region
    dsimp [KRKSevenSecond.RookRegion]
    omega

private theorem edge_eleven {sk rs : Square} (king : sk = ((3 : Fin 8),2) ∨ sk = ((2 : Fin 8),3))
    (apart : ((2 : Fin 8),2) ≠ rs) (x : 2 ≤ rs.1.val) (y : 2 ≤ rs.2.val)
    {j : Fin 8} (edge : j = 0 ∨ j = 1 ∨ j = 2) : KRKElevenGeometry.Clear sk rs (j,0) := by
  have old := diagonal_edge_eight apart x y edge
  have notWeak : rs ≠ (j,0) := by simp only [ne_iff_coords]; dsimp; omega
  have far : 2 ≤ dInf ((2 : Fin 8),2) (j,0) := by dsimp [dInf,absDiff]; omega
  exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2))
    (by rcases king with rfl | rfl <;> decide) apart far
    (KRKTwelveNearFileEntries.eight_region_subset apart notWeak far old)

/-- A broad evaluated rectangle, including all its protected-rook boundary cases. -/
theorem clear {rs : Square} (apart : ((3 : Fin 8),2) ≠ rs)
    (x : 2 ≤ rs.1.val) (y : 2 ≤ rs.2.val) : KRKTwelveGeometry.Clear (3,2) rs (1,1) := by
  by_cases diagonal : rs = ((2 : Fin 8),2)
  · rw [diagonal]
    exact KRKTwelveInner.ten_clear_subset (by decide) (by decide)
      (KRKTenInner.sufficient (Or.inl (Or.inl ⟨rfl,Or.inr (Or.inr ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩)⟩)))
  have distinct : ((2 : Fin 8),2) ≠ rs := Ne.symm diagonal
  have spread : 3 ≤ rs.1.val ∨ 3 ≤ rs.2.val := by
    simp only [ne_iff_coords] at diagonal
    dsimp at diagonal
    omega
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
        t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have west : ∀ {j : Fin 8}, j = 1 ∨ j = 2 →
        KRKCornerWeakBand.Guard ((3 : Fin 8),2) rs (1,1) (0,j) →
        KRKElevenGeometry.Clear (3,2) rs (0,j) := by
      intro j choice actualGuard
      let g := Frame.ofSym symSwap
      have source := edge_eleven (Or.inr rfl) (g.ne_iff.mpr distinct) y x (j := j)
        (by rcases choice with rfl | rfl <;> simp)
      have notKing : ((3 : Fin 8),2) ≠ (0,j) :=
        ne_of_dInf_pos (by have h := actualGuard.2.2.1; omega)
      have mapped := KRKElevenGeometry.frame_map g (g.ne_iff.mpr apart) (g.ne_iff.mpr notKing)
        (g.ne_iff.mpr actualGuard.2.1.symm)
        (by change 2 ≤ dInf (g.f ((3 : Fin 8),2)) (g.f ((0 : Fin 8),j)); rw [g.distance]; exact actualGuard.2.2.1)
        (fun h => actualGuard.2.2.2 ((g.sees _ _ _ _).mp h)) source
      simpa only [g,Frame.ofSym,symSwap] using mapped
    rcases targets with rfl | rfl | rfl | rfl | rfl | rfl
    · exact edge_eleven (Or.inl rfl) distinct x y (Or.inl rfl)
    · exact edge_eleven (Or.inl rfl) distinct x y (Or.inr (Or.inl rfl))
    · exact edge_eleven (Or.inl rfl) distinct x y (Or.inr (Or.inr rfl))
    · exact west (Or.inl rfl) guard
    · exact west (Or.inr rfl) guard
    · apply (KRKElevenNearStrip.clear_iff apart guard.2.1.symm).mpr
      refine Or.inr ⟨.side,rfl,Or.inl ?_⟩
      dsimp [KRKElevenNearStrip.SideRow]
      simp only [ne_iff_coords] at apart
      dsimp at apart
      omega

private theorem earlier_iff {rs : Square} (x : 2 ≤ rs.1.val) (y : 2 ≤ rs.2.val) :
    KRKTenInner.Region (3,2) rs ↔ rs = ((2 : Fin 8),2) ∨ (rs.2.val = 3 ∧ 3 ≤ rs.1.val) := by
  dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
    KRKTenInner.SideExtra,KRKTenInner.HighExtra,KRKNineNearStrip.RookCondition,symSwap]
  simp only [square_eq_iff,Fin.ext_iff]
  dsimp
  simp only [true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false]
  omega

theorem kernel_twelve {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,2) rs (1,1)) (turn : q.turn = σ.opp)
    (x : 2 ≤ rs.1.val) (y : 2 ≤ rs.2.val) : MateWithin σ 12 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr (clear material.1 x y)

theorem kernel_exact_twelve {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,2) rs (1,1)) (turn : q.turn = σ.opp)
    (x : 2 ≤ rs.1.val) (y : 2 ≤ rs.2.val) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔
      rs ≠ ((2 : Fin 8),2) ∧ ¬(rs.2.val = 3 ∧ 3 ≤ rs.1.val) := by
  constructor
  · rintro ⟨_,notEleven⟩
    have notOld : ¬KRKTenInner.Region (3,2) rs := by
      intro old
      have ten := (KRKTenInner.kernel_ten_iff material turn (by decide)).mpr old
      exact notEleven (mateWithin_mono ten (by decide))
    exact ⟨fun h => notOld ((earlier_iff x y).mpr (Or.inl h)),
      fun h => notOld ((earlier_iff x y).mpr (Or.inr h))⟩
  · rintro ⟨notDiagonal,notRow⟩
    refine ⟨kernel_twelve material turn x y,?_⟩
    intro eleven
    have old := (KRKTenInner.kernel_ten_iff material turn (by decide)).mp (KRKTenGeometry.weak_eleven_ten material turn eleven)
    rcases (earlier_iff x y).mp old with diagonal | row
    · exact notDiagonal diagonal
    · exact notRow row

end EndgameChess.Rules.KRKTwelveInnerHigh
