import EndgameChess.Rules.KRKTwelveCentralUpperEntries

namespace EndgameChess.Rules.KRKTwelveCentralUpper
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem upper_two_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 2)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) (high : 4 ≤ rs.2.val) :
    ¬KRKTwelveGeometry.Clear sk rs (1,3) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (0,3) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((0 : Fin 8),3) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have equal : g.f sk = ((5 : Fin 8),2) := Prod.ext (Fin.ext sy) (Fin.ext sx)
  rw [equal] at mapped
  exact KRKElevenEdgeBoundary.middle_five_two_not_eleven high rx mapped

theorem upper_one_high_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 1)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) (high : 5 ≤ rs.2.val) :
    ¬KRKTwelveGeometry.Clear sk rs (1,3) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (0,3) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((0 : Fin 8),3) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have equal : g.f sk = ((5 : Fin 8),1) := Prod.ext (Fin.ext sy) (Fin.ext sx)
  rw [equal] at mapped
  exact KRKElevenEdgeBoundary.middle_five_one_not_eleven high rx mapped

/-- The adjacent rook (2,4) is protected by king (1,5); it is a real
winning family and cannot be dropped by a distant-rook assumption. -/
theorem protected_clear : KRKTwelveGeometry.Clear ((1 : Fin 8),5) ((2 : Fin 8),4) (1,3) := by
  refine ⟨Or.inr (by decide),⟨((0 : Fin 8),2),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
    decide
  · intro t guard
    have targets : t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, 2 ≤ j.val → j.val ≤ 3 →
        KRKCornerWeakBand.Guard ((1 : Fin 8),5) ((2 : Fin 8),4) (1,3) (0,j) →
        KRKElevenGeometry.Clear ((1 : Fin 8),5) ((2 : Fin 8),4) (0,j) := by
      intro j low high guard
      let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f ((1 : Fin 8),5)) (g.f ((2 : Fin 8),4)) (g.f ((0 : Fin 8),j)) :=
        KRKTwelveCentralUpperEntries.edge_eleven low (by change j.val ≤ 4; omega)
      have back := KRKElevenGeometry.frame_map g.inverse (by decide)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl
    · exact edge (by decide) (by decide) guard
    · exact edge (by decide) (by decide) guard
    · apply (KRKElevenNearStrip.clear_iff (by decide) (by decide)).mpr
      exact Or.inl ⟨.upperOne,by decide,by decide,⟨rfl,by decide⟩⟩

theorem upper_one_iff {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 1)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) (high : 4 ≤ rs.2.val) :
    KRKTwelveGeometry.Clear sk rs (1,3) ↔ rs.2.val = 4 := by
  constructor
  · intro clear
    by_cases row : rs.2.val = 4
    · exact row
    · exact False.elim (upper_one_high_no_clear apart sx sy rx (by omega) clear)
  · intro row
    have kingEq : sk = ((1 : Fin 8),5) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),4) := Prod.ext (Fin.ext rx) (Fin.ext row)
    rw [kingEq,rookEq]
    exact protected_clear

theorem upper_zero_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 0)
    (sy : sk.2.val = 5) (rx : rs.1.val = 2) (high : 5 ≤ rs.2.val) :
    ¬KRKTwelveGeometry.Clear sk rs (1,3) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (0,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((0 : Fin 8),2) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have equal : g.f sk = ((5 : Fin 8),0) := Prod.ext (Fin.ext sy) (Fin.ext sx)
  rw [equal] at mapped
  exact KRKElevenEdgeBoundary.second_five_zero_not_eleven (by change 4 ≤ rs.2.val; omega) rx mapped

theorem upper_iff {sk rs : Square} (apart : sk ≠ rs) (sy : sk.2.val = 5)
    (sx : sk.1.val ≤ 2) (rx : rs.1.val = 2) :
    KRKTwelveGeometry.Clear sk rs (1,3) ↔ sk.1.val = 1 ∧ rs.2.val = 4 := by
  constructor
  · intro clear
    have condition := KRKTwelveCentralStrip.upper_necessary apart sy sx rx clear
    have files : sk.1.val = 0 ∨ sk.1.val = 1 ∨ sk.1.val = 2 := by omega
    rcases files with zero | one | two
    · exact False.elim (upper_zero_no_clear apart zero sy rx (by omega) clear)
    · exact ⟨one,(upper_one_iff apart one sy rx condition.1).mp clear⟩
    · exact False.elim (upper_two_no_clear apart two sy rx condition.1 clear)
  · rintro ⟨one,row⟩
    have kingEq : sk = ((1 : Fin 8),5) := Prod.ext (Fin.ext one) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),4) := Prod.ext (Fin.ext rx) (Fin.ext row)
    rw [kingEq,rookEq]
    exact protected_clear

theorem kernel_upper_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3))
    (sy : sk.2.val = 5) (sx : sk.1.val ≤ 2) (rx : rs.1.val = 2) :
    MateWithin σ 12 q ↔ sk.1.val = 1 ∧ rs.2.val = 4 := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans (upper_iff material.1 sy sx rx)

theorem kernel_upper_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3))
    (sy : sk.2.val = 5) (sx : sk.1.val ≤ 2) (rx : rs.1.val = 2) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ sk.1.val = 1 ∧ rs.2.val = 4 := by
  have notTen := KRKTenCentralStrip.middle_kernel_no_ten material turn
    (Or.inl ⟨Or.inl rfl,by decide,by decide⟩) far
  exact ⟨fun h => (kernel_upper_iff material turn far sy sx rx).mp h.1,fun region =>
    ⟨(kernel_upper_iff material turn far sy sx rx).mpr region,
      fun eleven => notTen (KRKTenGeometry.weak_eleven_ten material turn eleven)⟩⟩

end EndgameChess.Rules.KRKTwelveCentralUpper
