import EndgameChess.Rules.KRKTwelveInnerBoundaryEntries

namespace EndgameChess.Rules.KRKTwelveInnerHighExact
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Region (rs : Square) : Prop :=
  (2 ≤ rs.1.val ∧ 2 ≤ rs.2.val) ∨
  (rs.1.val = 1 ∧ 3 ≤ rs.2.val) ∨
  (rs.1.val = 0 ∧ 3 ≤ rs.2.val ∧ rs.2.val ≤ 5) ∨
  (4 ≤ rs.1.val ∧ rs.2.val ≤ 1) ∨ rs = ((2 : Fin 8),1)

theorem necessary {rs : Square} (apart : ((3 : Fin 8),2) ≠ rs)
    (clear : KRKTwelveGeometry.Clear (3,2) rs (1,1)) : Region rs := by
  have safe := clear.1
  by_cases file : rs.1.val = 1
  · have high : 3 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    exact Or.inr (Or.inl ⟨file,high⟩)
  by_cases row : rs.2.val = 2
  · have width : 2 ≤ rs.1.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    exact Or.inl ⟨width,by omega⟩
  have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),2) rs (1,1) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  have evaluated := (KRKElevenNearStrip.clear_iff apart guard.2.1.symm).mp (clear.2.2 _ guard)
  dsimp [SafeRook,dInf,absDiff] at safe
  rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
  · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,dInf,absDiff] at distance shape <;>
      dsimp [Region] <;> simp only [square_eq_iff,Fin.ext_iff] <;> dsimp <;> omega
  · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;>
      (try dsimp at equal) <;>
      dsimp [KRKElevenNearStrip.RookCondition,KRKNineNearStrip.RookCondition,
        KRKElevenNearStrip.SideRow,KRKElevenNearStrip.SideFile] at condition <;>
      dsimp [Region] <;> simp only [square_eq_iff,Fin.ext_iff] <;> dsimp <;> omega

private theorem zero_clear {h : Fin 8} (bounds : 3 ≤ h.val ∧ h.val ≤ 5) :
    KRKTwelveGeometry.Clear (3,2) (0,h) (1,1) := by
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((1 : Fin 8),0),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro t guard
    have targets : t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, j = 1 ∨ j = 2 → KRKElevenGeometry.Clear (3,2) (0,h) (j,0) := by
      intro j choice
      have apart : ((2 : Fin 8),2) ≠ (0,h) := by simp
      have far : 2 ≤ dInf ((2 : Fin 8),2) (j,0) := by dsimp [dInf,absDiff]; omega
      have old : KRKEightGlobal.Region (2,2) (0,h) (j,0) := by
        rcases choice with rfl | rfl
        · exact KRKEightDiagonalEntries.near_region apart (Or.inl (by dsimp [dInf,absDiff]; omega))
        · exact KRKEightDiagonalEntries.second_region (Or.inl bounds.1)
      exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) apart far
        (KRKTwelveNearFileEntries.eight_region_subset apart (by simp only [ne_iff_coords]; (try dsimp); omega) far old)
    rcases targets with rfl | rfl | rfl
    · exact edge (Or.inl rfl)
    · exact edge (Or.inr rfl)
    · apply (KRKElevenNearStrip.clear_iff (by simp) (by simp)).mpr
      refine Or.inr ⟨.side,rfl,?_⟩
      dsimp [KRKElevenNearStrip.RookCondition,KRKElevenNearStrip.SideRow,KRKElevenNearStrip.SideFile]
      omega

private theorem low_clear {x y : Fin 8} (width : 4 ≤ x.val) (height : y.val ≤ 1) :
    KRKTwelveGeometry.Clear (3,2) (x,y) (1,1) := by
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),2),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
        t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have apart : ((2 : Fin 8),2) ≠ (x,y) := by simp only [ne_iff_coords]; (try dsimp); omega
    have bottom : ∀ {j : Fin 8}, j = 0 ∨ j = 1 → KRKElevenGeometry.Clear (3,2) (x,y) (j,0) := by
      intro j choice
      have far : 2 ≤ dInf ((2 : Fin 8),2) (j,0) := by dsimp [dInf,absDiff]; omega
      have old : KRKEightGlobal.Region (2,2) (x,y) (j,0) := by
        rcases choice with rfl | rfl
        · exact KRKEightDiagonalEntries.corner_region (by dsimp [dInf,absDiff]; omega)
        · exact KRKEightDiagonalEntries.near_region apart (Or.inl (by dsimp [dInf,absDiff]; omega))
      exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) apart far
        (KRKTwelveNearFileEntries.eight_region_subset apart (by simp only [ne_iff_coords]; (try dsimp); omega) far old)
    have west : ∀ {j : Fin 8}, j = 1 ∨ j = 2 →
        KRKCornerWeakBand.Guard ((3 : Fin 8),2) (x,y) (1,1) (0,j) → KRKElevenGeometry.Clear (3,2) (x,y) (0,j) := by
      intro j choice actual
      let g := Frame.ofSym symSwap
      have source : KRKElevenGeometry.Clear (2,3) (y,x) (j,0) := by
        have distinct : ((2 : Fin 8),2) ≠ (y,x) := by simp only [ne_iff_coords]; (try dsimp); omega
        have far : 2 ≤ dInf ((2 : Fin 8),2) (j,0) := by dsimp [dInf,absDiff]; omega
        have old : KRKEightGlobal.Region (2,2) (y,x) (j,0) := by
          rcases choice with rfl | rfl
          · exact KRKEightDiagonalEntries.near_region distinct (Or.inl (by dsimp [dInf,absDiff]; omega))
          · exact KRKEightDiagonalEntries.second_region (rs := ((y : Fin 8),x)) (Or.inl (by change 3 ≤ x.val; omega))
        exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) distinct far
          (KRKTwelveNearFileEntries.eight_region_subset distinct (by simp only [ne_iff_coords]; (try dsimp); omega) far old)
      have notKing : ((3 : Fin 8),2) ≠ (0,j) := ne_of_dInf_pos (by have h := actual.2.2.1; omega)
      have mapped := KRKElevenGeometry.frame_map g (by simp only [ne_iff_coords]; dsimp [g,Frame.ofSym,symSwap]; omega)
        (g.ne_iff.mpr notKing) (g.ne_iff.mpr actual.2.1.symm)
        (by change 2 ≤ dInf (g.f ((3 : Fin 8),2)) (g.f ((0 : Fin 8),j)); rw [g.distance]; exact actual.2.2.1)
        (fun h => actual.2.2.2 ((g.sees _ _ _ _).mp h)) source
      simpa only [g,Frame.ofSym,symSwap] using mapped
    rcases targets with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bottom (Or.inl rfl)
    · exact bottom (Or.inr rfl)
    · have one : y.val = 1 := by
        simp only [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        dsimp at guard
        omega
      have yEq : y = 1 := Fin.ext one
      rw [yEq]
      by_cases four : x = 4
      · rw [four]
        have old := KRKEightDiagonalEntries.second_region (rs := ((4 : Fin 8),1))
          (Or.inr (Or.inr ⟨rfl,Or.inr rfl⟩))
        exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide)
          (KRKTwelveNearFileEntries.eight_region_subset (by decide) (by decide) (by decide) old)
      · exact KRKElevenGeometry.rook_step_clear (nr := ((4 : Fin 8),1))
          (by simp only [RookSees,RookLine,OnSeg,ne_iff_coords]; (try dsimp); simp only [Fin.ext_iff] at four; (try dsimp at four); simp only [show ((4 : Fin 8).val) = 4 from rfl,show ((3 : Fin 8).val) = 3 from rfl] at four ⊢; simp_all)
          (by decide) (by decide) KRKTwelveInnerBoundaryEntries.low_second
    · exact west (Or.inl rfl) guard
    · exact west (Or.inr rfl) guard
    · apply (KRKElevenNearStrip.clear_iff (by simp only [ne_iff_coords]; (try dsimp); omega) guard.2.1.symm).mpr
      exact Or.inr ⟨.side,rfl,Or.inl (Or.inr (Or.inr (Or.inl width)))⟩

theorem sufficient {rs : Square} (apart : ((3 : Fin 8),2) ≠ rs) (region : Region rs) :
    KRKTwelveGeometry.Clear (3,2) rs (1,1) := by
  rcases region with ⟨x,y⟩ | ⟨file,height⟩ | ⟨file,low,high⟩ | ⟨width,height⟩ | equal
  · exact KRKTwelveInnerHigh.clear apart x y
  · have old : KRKTenInner.Region (3,2) rs :=
      Or.inl (Or.inl ⟨rfl,Or.inr (Or.inr ⟨rfl,Or.inr ⟨file,height⟩⟩)⟩)
    exact KRKTwelveInner.ten_clear_subset apart (by decide) (KRKTenInner.sufficient old)
  · have equal : rs = ((0 : Fin 8),rs.2) := Prod.ext (Fin.ext file) rfl
    rw [equal]
    exact zero_clear ⟨low,high⟩
  · exact low_clear width height
  · rw [equal]
    exact KRKTwelveInnerBoundaryEntries.protected_clear

theorem clear_iff {rs : Square} (apart : ((3 : Fin 8),2) ≠ rs) :
    KRKTwelveGeometry.Clear (3,2) rs (1,1) ↔ Region rs := ⟨necessary apart,sufficient apart⟩

theorem kernel_twelve_iff {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,2) rs (1,1)) (turn : q.turn = σ.opp) : MateWithin σ 12 q ↔ Region rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans (clear_iff material.1)

theorem kernel_exact_twelve {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,2) rs (1,1)) (turn : q.turn = σ.opp) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region rs ∧ ¬KRKTenInner.Region (3,2) rs := by
  constructor
  · rintro ⟨twelve,notEleven⟩
    refine ⟨(kernel_twelve_iff material turn).mp twelve,?_⟩
    intro old
    exact notEleven (mateWithin_mono ((KRKTenInner.kernel_ten_iff material turn (by decide)).mpr old) (by decide))
  · rintro ⟨region,notOld⟩
    exact ⟨(kernel_twelve_iff material turn).mpr region,fun eleven =>
      notOld ((KRKTenInner.kernel_ten_iff material turn (by decide)).mp (KRKTenGeometry.weak_eleven_ten material turn eleven))⟩

end EndgameChess.Rules.KRKTwelveInnerHighExact
