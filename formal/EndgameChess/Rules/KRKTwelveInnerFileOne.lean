import EndgameChess.Rules.KRKTwelveInnerDiagonal

namespace EndgameChess.Rules.KRKTwelveInnerFileOne
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem high_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 1) (rx : rs.1.val = 1) (high : 6 ≤ rs.2.val) :
    ¬KRKTwelveGeometry.Clear sk rs (1,1) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,1) (0,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((0 : Fin 8),2) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have equal : g.f sk = ((1 : Fin 8),3) := Prod.ext (Fin.ext sy) (Fin.ext sx)
  rw [equal] at mapped
  exact KRKElevenEdgeBoundary.second_one_three_high_rook_not_eleven high rx mapped

private theorem middle_eight : KRKEightGlobal.Region ((3 : Fin 8),2) ((5 : Fin 8),1) (3,0) := by
  change KRKEightEdge.Region ((3 : Fin 8),2) ((5 : Fin 8),1) (3,0)
  refine ⟨Or.inl (by decide),⟨.west,?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]
    decide
  · intro i guard
    cases i with
    | west => exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inr ⟨.east,rfl,True.intro⟩⟩))
    | east =>
      have five : KRKFiveMiddle.BottomFive ((3 : Fin 8),2) ((5 : Fin 8),1) (4,0) := by
        change KRKFiveMiddle.Five ((4 : Fin 8),2) ((2 : Fin 8),1) (3,0)
        exact Or.inr (Or.inr (Or.inr ⟨rfl,Or.inl rfl⟩))
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl,five⟩)))
    | northWest =>
      have far := guard.2.2.1
      change 2 ≤ dInf ((3 : Fin 8),2) (2,1) at far
      contradiction
    | north =>
      have far := guard.2.2.1
      change 2 ≤ dInf ((3 : Fin 8),2) (3,1) at far
      contradiction
    | northEast =>
      have far := guard.2.2.1
      change 2 ≤ dInf ((3 : Fin 8),2) (4,1) at far
      contradiction

private theorem middle_nine : KRKNineGeometry.Clear ((2 : Fin 8),2) ((5 : Fin 8),1) (3,0) :=
  KRKNineGeometry.king_step_clear (ns := ((3 : Fin 8),2)) (by decide) (by decide) (by decide) middle_eight

private theorem near_nine : KRKNineGeometry.Clear ((2 : Fin 8),2) ((5 : Fin 8),1) (1,0) :=
  KRKNineGeometry.rook_step_clear (nr := ((3 : Fin 8),1))
    (by dsimp [RookSees,RookLine,OnSeg]; decide) (by decide) (by decide)
    (KRKEightDiagonalEntries.near_region (by decide) (Or.inl (by decide)))

private theorem second_ten : KRKTenGlobal.Region ((2 : Fin 8),2) ((5 : Fin 8),1) (2,0) := by
  have clear : KRKTenGeometry.Clear ((2 : Fin 8),2) ((5 : Fin 8),1) (2,0) := by
    refine ⟨Or.inl (by decide),⟨((1 : Fin 8),0),?_⟩,?_⟩
    · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
      decide
    · intro t guard
      have targets : t = ((1 : Fin 8),0) ∨ t = ((3 : Fin 8),0) := by
        simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
        simp only [square_eq_iff,Fin.ext_iff]
        dsimp at guard ⊢
        omega
      rcases targets with rfl | rfl
      · exact near_nine
      · exact middle_nine
  exact (KRKTenGlobal.edge_clear_iff (by decide) (by decide)).mp clear

private theorem bottom_eleven {j : Fin 8} (choice : j = 0 ∨ j = 1 ∨ j = 2) :
    KRKElevenGeometry.Clear ((1 : Fin 8),3) ((5 : Fin 8),1) (j,0) := by
  rcases choice with rfl | rfl | rfl
  · have region := KRKTwelveNearFileEntries.eight_region_subset (by decide) (by decide) (by decide)
      (KRKEightDiagonalEntries.corner_region (rs := ((5 : Fin 8),1)) (by decide))
    exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide) region
  · have region := KRKTwelveNearFileEntries.eight_region_subset (by decide) (by decide) (by decide)
      (KRKEightDiagonalEntries.near_region (rs := ((5 : Fin 8),1)) (by decide) (Or.inl (by decide)))
    exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide) region
  · exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) (by decide) (by decide) second_ten

theorem five_clear : KRKTwelveGeometry.Clear ((3 : Fin 8),1) ((1 : Fin 8),5) (1,1) := by
  refine ⟨Or.inl (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
    decide
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, j = 0 ∨ j = 1 ∨ j = 2 →
        KRKCornerWeakBand.Guard ((3 : Fin 8),1) ((1 : Fin 8),5) (1,1) (0,j) →
        KRKElevenGeometry.Clear ((3 : Fin 8),1) ((1 : Fin 8),5) (0,j) := by
      intro j choice guard
      let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f ((3 : Fin 8),1)) (g.f ((1 : Fin 8),5)) (g.f ((0 : Fin 8),j)) :=
        bottom_eleven choice
      have back := KRKElevenGeometry.frame_map g.inverse (by decide)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl
    · exact edge (Or.inl rfl) guard
    · exact edge (Or.inr (Or.inl rfl)) guard
    · exact edge (Or.inr (Or.inr rfl)) guard

theorem kernel_exact_twelve {q : Position} {σ : Colour}
    (material : IsKRK q σ (3,1) (1,5) (1,1)) (turn : q.turn = σ.opp) :
    MateWithin σ 12 q ∧ ¬MateWithin σ 11 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  refine ⟨(KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr five_clear,?_⟩
  intro eleven
  have ten := KRKTenGeometry.weak_eleven_ten material turn eleven
  have region := (KRKTenInner.kernel_ten_iff material turn (by decide)).mp ten
  dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
    KRKTenInner.SideExtra,KRKTenInner.HighExtra,KRKNineNearStrip.RookCondition,symSwap] at region
  omega

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 1) (rx : rs.1.val = 1) :
    KRKTwelveGeometry.Clear sk rs (1,1) ↔ 3 ≤ rs.2.val ∧ rs.2.val ≤ 5 := by
  constructor
  · intro clear
    have safe := clear.1
    have low : 3 ≤ rs.2.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    have notHigh : ¬6 ≤ rs.2.val := fun high => high_no_clear apart sx sy rx high clear
    exact ⟨low,by omega⟩
  · rintro ⟨low,high⟩
    by_cases five : rs.2.val = 5
    · have kingEq : sk = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      have rookEq : rs = ((1 : Fin 8),5) := Prod.ext (Fin.ext rx) (Fin.ext five)
      rw [kingEq,rookEq]
      exact five_clear
    · have old : KRKTenInner.Region sk rs :=
        Or.inl (Or.inl ⟨sx,Or.inr (Or.inl ⟨sy,Or.inr ⟨rx,low,by omega⟩⟩)⟩)
      have far : 2 ≤ dInf sk (1,1) := by dsimp [dInf,absDiff]; omega
      exact KRKTwelveInner.ten_clear_subset apart far (KRKTenInner.sufficient old)

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1))
    (sx : sk.1.val = 3) (sy : sk.2.val = 1) (rx : rs.1.val = 1) :
    MateWithin σ 12 q ↔ 3 ≤ rs.2.val ∧ rs.2.val ≤ 5 := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans (clear_iff material.1 sx sy rx)

theorem kernel_height_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1))
    (sx : sk.1.val = 3) (sy : sk.2.val = 1) (rx : rs.1.val = 1) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ rs.2.val = 5 := by
  constructor
  · rintro ⟨twelve,notEleven⟩
    have height := (kernel_twelve_iff material turn far sx sy rx).mp twelve
    by_cases five : rs.2.val = 5
    · exact five
    · have old : KRKTenInner.Region sk rs :=
        Or.inl (Or.inl ⟨sx,Or.inr (Or.inl ⟨sy,Or.inr ⟨rx,height.1,by omega⟩⟩)⟩)
      have ten := (KRKTenInner.kernel_ten_iff material turn far).mpr old
      exact False.elim (notEleven (mateWithin_mono ten (by decide)))
  · intro five
    have kingEq : sk = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = ((1 : Fin 8),5) := Prod.ext (Fin.ext rx) (Fin.ext five)
    rw [kingEq,rookEq] at material
    exact kernel_exact_twelve material turn

end EndgameChess.Rules.KRKTwelveInnerFileOne
