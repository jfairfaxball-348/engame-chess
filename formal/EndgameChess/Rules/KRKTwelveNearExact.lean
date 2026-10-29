import EndgameChess.Rules.KRKTwelveNearUpper

namespace EndgameChess.Rules.KRKTwelveNearExact
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def RowTwo (sk rs : Square) : Prop :=
  sk.2.val = 4 ∧ (sk.1.val = 1 ∨ sk.1.val = 2) ∧ rs.1.val = 3 ∧ rs.2.val = 2

theorem row_two_clear {sk rs : Square} (region : RowTwo sk rs) : KRKTwelveGeometry.Clear sk rs (1,2) := by
  obtain ⟨sy,files,rx,ry⟩ := region
  have rookEq : rs = ((3 : Fin 8),2) := Prod.ext (Fin.ext rx) (Fin.ext ry)
  subst rs
  let k := sk.1
  have kingEq : sk = (k,(4 : Fin 8)) := Prod.ext rfl (Fin.ext sy)
  have choice : k = 1 ∨ k = 2 := by
    rcases files with one | two
    · exact Or.inl (Fin.ext one)
    · exact Or.inr (Fin.ext two)
  rw [kingEq]
  have distinct : (k,(4 : Fin 8)) ≠ ((3 : Fin 8),2) := by simp [ne_iff_coords]
  refine ⟨Or.inl (by decide),⟨((0 : Fin 8),1),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    rcases choice with one | two
    · rw [one]; decide
    · rw [two]; decide
  · intro t guard
    have targets : t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),3) ∨
        t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      have width : k.val = 1 ∨ k.val = 2 := by
        rcases choice with one | two
        · exact Or.inl (congrArg Fin.val one)
        · exact Or.inr (congrArg Fin.val two)
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, j = 1 ∨ j = 3 →
        KRKCornerWeakBand.Guard (k,(4 : Fin 8)) ((3 : Fin 8),2) (1,2) (0,j) →
        KRKElevenGeometry.Clear (k,(4 : Fin 8)) ((3 : Fin 8),2) (0,j) := by
      intro j jChoice guard
      let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f (k,(4 : Fin 8))) (g.f ((3 : Fin 8),2)) (g.f ((0 : Fin 8),j)) := by
        rcases jChoice with rfl | rfl
        · exact KRKTwelveNearNewEntries.row_near_eleven choice
        · exact KRKTwelveNearNewEntries.row_middle_eleven choice
      have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl | rfl
    · exact edge (Or.inl rfl) guard
    · exact edge (Or.inr rfl) guard
    · exact KRKTwelveNearNewEntries.row_inner_eleven choice
    · let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f (k,(4 : Fin 8))) (g.f ((3 : Fin 8),2)) (g.f ((2 : Fin 8),1)) :=
        KRKTwelveNearNewEntries.row_lower_eleven choice
      have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back

def Region (sk rs : Square) : Prop :=
  KRKEightStrip.Region sk rs (1,2) ∨ KRKTenNearStrip.RowThree sk rs ∨
    KRKTwelveNearFileOne.Region sk rs ∨ KRKTwelveNearUpper.Region sk rs ∨ RowTwo sk rs

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,2))
    (clear : KRKTwelveGeometry.Clear sk rs (1,2)) : Region sk rs := by
  rcases KRKTwelveNearStrip.prison apart far clear with
    ⟨sx,sy,ry⟩ | ⟨sx,sy,rx⟩ | ⟨sy,sx,rx⟩ | ⟨sy,sx,ry⟩ | ⟨sx,sy,rx,ry⟩
  · rcases KRKTwelveNearStrip.row_three_necessary apart sx sy ry clear with old | row
    · exact Or.inl old
    · exact Or.inr (Or.inl row)
  · exact Or.inr (Or.inr (Or.inl (KRKTwelveNearFileOne.necessary apart sx sy rx clear)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (KRKTwelveNearUpper.necessary apart sy sx rx clear))))
  · have safe := clear.1
    have width : 3 ≤ rs.1.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    have file := KRKTwelveNearStrip.row_two_necessary apart sy sx ry width clear
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨sy,sx,file,ry⟩)))
  · have kingEq : sk = ((3 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),3) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    rw [kingEq,rookEq] at clear
    exact False.elim (KRKTwelveNearStrip.protected_high_no_clear clear)

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTwelveGeometry.Clear sk rs (1,2) := by
  rcases region with old | row | file | upper | rowTwo
  · have apart : sk ≠ rs := by dsimp [KRKEightStrip.Region] at old; simp only [ne_iff_coords]; omega
    have far : 2 ≤ dInf sk (1,2) := by dsimp [KRKEightStrip.Region,dInf,absDiff] at old ⊢; omega
    exact KRKTwelveNearUpper.ten_clear_subset apart far (KRKTenNearStrip.sufficient (Or.inl old))
  · have apart : sk ≠ rs := by dsimp [KRKTenNearStrip.RowThree] at row; simp only [ne_iff_coords]; omega
    have far : 2 ≤ dInf sk (1,2) := by dsimp [KRKTenNearStrip.RowThree,dInf,absDiff] at row ⊢; omega
    exact KRKTwelveNearUpper.ten_clear_subset apart far (KRKTenNearStrip.sufficient (Or.inr (Or.inl row)))
  · exact KRKTwelveNearFileOne.sufficient file
  · exact KRKTwelveNearUpper.sufficient upper
  · exact row_two_clear rowTwo

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2)) :
    MateWithin σ 12 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans ⟨necessary material.1 far,sufficient⟩

theorem kernel_exact_twelve_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2)) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region sk rs ∧ ¬KRKTenNearStrip.Region sk rs := by
  constructor
  · rintro ⟨twelve,notEleven⟩
    exact ⟨(kernel_twelve_iff material turn far).mp twelve,fun tenRegion =>
      notEleven (mateWithin_mono ((KRKTenNearStrip.kernel_ten_iff material turn far).mpr tenRegion) (by decide))⟩
  · rintro ⟨region,notTen⟩
    exact ⟨(kernel_twelve_iff material turn far).mpr region,fun eleven =>
      notTen ((KRKTenNearStrip.kernel_ten_iff material turn far).mp
        (KRKTenGeometry.weak_eleven_ten material turn eleven))⟩

def Fresh (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.1.val = 1 ∧ (rs.2.val = 0 ∨ 6 ≤ rs.2.val)) ∨
  (sk.1.val = 2 ∧ sk.2.val = 4 ∧ rs.1.val = 2 ∧ rs.2.val = 3) ∨ RowTwo sk rs

theorem fresh_iff {sk rs : Square} : Region sk rs ∧ ¬KRKTenNearStrip.Region sk rs ↔ Fresh sk rs := by
  constructor
  · rintro ⟨region,notTen⟩
    rcases region with old | row | ⟨sx,sy,rx,height⟩ | upper | rowTwo
    · exact False.elim (notTen (Or.inl old))
    · exact False.elim (notTen (Or.inr (Or.inl row)))
    · have notMiddle : ¬(rs.2.val = 4 ∨ rs.2.val = 5) := by
        intro heights
        exact notTen (Or.inr (Or.inr (Or.inl ⟨sx,sy,rx,heights⟩)))
      exact Or.inl ⟨sx,sy,rx,by omega⟩
    · obtain ⟨sy,rx,zero | one | two⟩ := upper
      · exact False.elim (notTen (Or.inr (Or.inr (Or.inr ⟨sy,rx,Or.inl zero⟩))))
      · exact False.elim (notTen (Or.inr (Or.inr (Or.inr ⟨sy,rx,Or.inr one⟩))))
      · exact Or.inr (Or.inl ⟨two.1,sy,rx,two.2⟩)
    · exact Or.inr (Or.inr rowTwo)
  · rintro (⟨sx,sy,rx,height⟩ | ⟨sx,sy,rx,ry⟩ | rowTwo)
    · refine ⟨Or.inr (Or.inr (Or.inl ⟨sx,sy,rx,by omega⟩)),?_⟩
      intro shape
      dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
        KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper] at shape
      omega
    · refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨sy,rx,Or.inr (Or.inr ⟨sx,ry⟩)⟩))),?_⟩
      intro shape
      dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
        KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper] at shape
      omega
    · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr rowTwo))),?_⟩
      intro shape
      dsimp [RowTwo] at rowTwo
      dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
        KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper] at shape
      omega

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2)) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Fresh sk rs :=
  (kernel_exact_twelve_iff material turn far).trans fresh_iff

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),2))
    (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKTwelveGeometry.Clear sk rs wk ↔ Region (g.f sk) (g.f rs) := by
  constructor
  · intro clear
    have mapped := KRKTwelveGeometry.frame_map g apart clear
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    rw [target] at mapped mappedFar
    exact necessary (g.ne_iff.mpr apart) mappedFar mapped
  · intro region
    have mapped := sufficient region
    have shaped : KRKTwelveGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKTwelveGeometry.frame_map g.inverse (g.ne_iff.mpr apart) shaped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKTwelveNearExact
