import EndgameChess.Rules.KRKFourteenCentralUpperTwo

namespace EndgameChess.Rules.KRKFourteenCentralExact
open EndgameChess.KK KRKNativeFrame
open KRKFourteenCentralNecessary (Opposition Upper)

abbrev Region (sk rs : Square) : Prop := KRKFourteenCentralNecessary.Region sk rs
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

def FreshUpper (sk rs : Square) : Prop := sk.2.val = 5 ∧ rs.1.val = 2 ∧
  ((sk.1.val ≤ 1 ∧ 5 ≤ rs.2.val) ∨ (sk.1.val = 2 ∧ rs.2.val = 4))

def Fresh (sk rs : Square) : Prop := Opposition sk rs ∨ FreshUpper sk rs

private theorem old_subset {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKTwelveGeometry.Clear sk rs (1,3)) : KRKFourteenGeometry.Clear sk rs (1,3) := by
  have notRook : rs ≠ ((1 : Fin 8),3) := by
    intro equal
    have safe := clear.1
    rw [equal] at safe
    dsimp [SafeRook,dInf,absDiff] at safe far
    omega
  let q := krkPos .white sk rs (1,3) .black
  have material : IsKRK q .white sk rs (1,3) := ⟨apart,ne_of_dInf_pos (by omega),notRook,rfl⟩
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material rfl far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKFourteenGeometry.kernel_fourteen_iff material rfl notMate).mp
    (mateWithin_mono ((KRKTwelveGeometry.kernel_twelve_iff material rfl notMate).mpr clear) (by decide))

theorem sufficient {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,3)) (region : Region sk rs) :
    KRKFourteenGeometry.Clear sk rs (1,3) := by
  rcases region with old | opposition | ⟨sy,rx,zero | one | two⟩
  · exact old_subset apart far (KRKTwelveCentralExact.sufficient old)
  · obtain ⟨sx,sy,ry,width⟩ := opposition
    have kingEq : sk = ((3 : Fin 8),4) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = (rs.1,(2 : Fin 8)) := Prod.ext rfl (Fin.ext ry)
    rw [kingEq,rookEq]
    exact KRKFourteenCentralEntries.opposition_clear width
  · have kingEq : sk = ((0 : Fin 8),5) := Prod.ext (Fin.ext zero.1) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),rs.2) := Prod.ext (Fin.ext rx) rfl
    rw [kingEq,rookEq]
    exact KRKFourteenCentralUpperZero.clear zero.2
  · have kingEq : sk = ((1 : Fin 8),5) := Prod.ext (Fin.ext one.1) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),rs.2) := Prod.ext (Fin.ext rx) rfl
    rw [kingEq,rookEq]
    by_cases four : rs.2.val = 4
    · have eq : rs.2 = 4 := Fin.ext four
      rw [eq]
      exact old_subset (by decide) (by decide) (KRKTwelveCentralExact.sufficient (Or.inr (Or.inl ⟨rfl,rfl⟩)))
    · exact KRKFourteenCentralUpperEntries.upper_one_clear (by omega)
  · have kingEq : sk = ((2 : Fin 8),5) := Prod.ext (Fin.ext two.1) (Fin.ext sy)
    have rookEq : rs = ((2 : Fin 8),4) := Prod.ext (Fin.ext rx) (Fin.ext two.2)
    rw [kingEq,rookEq]
    exact KRKFourteenCentralUpperTwo.clear

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,3)) :
    KRKFourteenGeometry.Clear sk rs (1,3) ↔ Region sk rs :=
  ⟨KRKFourteenCentralNecessary.necessary apart far,sufficient apart far⟩

theorem fresh_iff {sk rs : Square} : Region sk rs ∧ ¬KRKTwelveCentralExact.Region sk rs ↔ Fresh sk rs := by
  constructor
  · rintro ⟨region,notOld⟩
    rcases region with old | opposition | ⟨sy,rx,zero | one | two⟩
    · exact False.elim (notOld old)
    · exact Or.inl opposition
    · exact Or.inr ⟨sy,rx,Or.inl ⟨by omega,zero.2⟩⟩
    · have notFour : rs.2.val ≠ 4 := by
        intro four
        have kingEq : sk = ((1 : Fin 8),5) := Prod.ext (Fin.ext one.1) (Fin.ext sy)
        have rookEq : rs = ((2 : Fin 8),4) := Prod.ext (Fin.ext rx) (Fin.ext four)
        exact notOld (Or.inr (Or.inl ⟨kingEq,rookEq⟩))
      exact Or.inr ⟨sy,rx,Or.inl ⟨by omega,by omega⟩⟩
    · exact Or.inr ⟨sy,rx,Or.inr two⟩
  · rintro (opposition | ⟨sy,rx,low | two⟩)
    · refine ⟨Or.inr (Or.inl opposition),?_⟩
      intro old
      obtain ⟨sx,sy,ry,width⟩ := opposition
      dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,KRKTwelveCentralExact.Opposition] at old
      simp only [square_eq_iff,Fin.ext_iff] at old
      (try dsimp at old)
      omega
    · have choice : sk.1.val = 0 ∨ sk.1.val = 1 := by omega
      have upper : Upper sk rs := by
        refine ⟨sy,rx,?_⟩
        rcases choice with zero | one
        · exact Or.inl ⟨zero,low.2⟩
        · exact Or.inr (Or.inl ⟨one,by omega⟩)
      refine ⟨Or.inr (Or.inr upper),?_⟩
      intro old
      dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,KRKTwelveCentralExact.Opposition] at old
      simp only [square_eq_iff,Fin.ext_iff] at old
      (try dsimp at old)
      simp only [show ((4 : Fin 8).val) = 4 from rfl] at old
      omega
    · refine ⟨Or.inr (Or.inr ⟨sy,rx,Or.inr (Or.inr two)⟩),?_⟩
      intro old
      dsimp [KRKTwelveCentralExact.Region,KRKTwelveCentralStrip.RowFour,KRKTwelveCentralExact.Protected,KRKTwelveCentralExact.Opposition] at old
      simp only [square_eq_iff,Fin.ext_iff] at old
      (try dsimp at old)
      omega

theorem kernel_fourteen_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3)) :
    MateWithin σ 14 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKFourteenGeometry.kernel_fourteen_iff material turn notMate).trans (clear_iff material.1 far)

theorem kernel_exact_fourteen {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3)) :
    (MateWithin σ 14 q ∧ ¬MateWithin σ 13 q) ↔ Fresh sk rs := by
  have earlier : MateWithin σ 12 q ↔ KRKTwelveCentralExact.Region sk rs := KRKTwelveCentralExact.kernel_twelve_iff material turn far
  apply Iff.trans (b := Region sk rs ∧ ¬KRKTwelveCentralExact.Region sk rs)
  · constructor
    · rintro ⟨fourteen,notThirteen⟩
      exact ⟨(kernel_fourteen_iff material turn far).mp fourteen,fun old => notThirteen (mateWithin_mono (earlier.mpr old) (by decide))⟩
    · rintro ⟨region,notOld⟩
      exact ⟨(kernel_fourteen_iff material turn far).mpr region,fun thirteen =>
        notOld (earlier.mp (KRKTwelveGeometry.weak_thirteen_twelve material turn thirteen))⟩
  · exact fresh_iff

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),3))
    (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKFourteenGeometry.Clear sk rs wk ↔ Region (g.f sk) (g.f rs) := by
  constructor
  · intro clear
    have mapped := KRKFourteenGeometry.frame_map g apart clear
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    rw [target] at mapped mappedFar
    exact KRKFourteenCentralNecessary.necessary (g.ne_iff.mpr apart) mappedFar mapped
  · intro region
    have mappedFar : 2 ≤ dInf (g.f sk) ((1 : Fin 8),3) := by rw [←target,g.distance]; exact far
    have mapped := sufficient (g.ne_iff.mpr apart) mappedFar region
    have shaped : KRKFourteenGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKFourteenGeometry.frame_map g.inverse (g.ne_iff.mpr apart) shaped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKFourteenCentralExact
