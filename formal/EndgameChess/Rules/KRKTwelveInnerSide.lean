import EndgameChess.Rules.KRKTwelveInnerOuter

namespace EndgameChess.Rules.KRKTwelveInnerSide
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

/-- Complete rook inequalities for strong king (3,1), weak king (1,1). -/
def Region (rs : Square) : Prop :=
  (rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨
  (rs.1.val = 1 ∧ 3 ≤ rs.2.val ∧ rs.2.val ≤ 5) ∨ KRKNineNearStrip.RookCondition rs

theorem necessary {rs : Square} (apart : ((3 : Fin 8),1) ≠ rs)
    (clear : KRKTwelveGeometry.Clear (3,1) rs (1,1)) : Region rs := by
  by_cases file : rs.1.val = 1
  · have height := (KRKTwelveInnerFileOne.clear_iff apart rfl rfl file).mp clear
    exact Or.inr (Or.inl ⟨file,height⟩)
  by_cases row : rs.2.val = 2
  · have safe := clear.1
    have width : 2 ≤ rs.1.val := by dsimp [SafeRook,dInf,absDiff] at safe; omega
    exact Or.inl ⟨row,width⟩
  have guard : KRKCornerWeakBand.Guard ((3 : Fin 8),1) rs (1,1) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp; omega
  have evaluated := (KRKElevenNearStrip.clear_iff apart guard.2.1.symm).mp (clear.2.2 _ guard)
  rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
  · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,dInf,absDiff] at distance shape <;>
      dsimp [Region,KRKNineNearStrip.RookCondition] <;> omega
  · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;>
      (try dsimp at equal) <;> dsimp [KRKElevenNearStrip.RookCondition,KRKNineNearStrip.RookCondition] at condition <;>
      dsimp [Region,KRKNineNearStrip.RookCondition] <;> omega

private theorem old_of_not_fresh {rs : Square} (region : Region rs)
    (notFresh : ¬(rs.1.val = 1 ∧ rs.2.val = 5)) : KRKTenInner.Region (3,1) rs := by
  rcases region with row | ⟨file,low,high⟩ | condition
  · exact Or.inl (Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inl row⟩)⟩)
  · have short : rs.2.val ≤ 4 := by omega
    exact Or.inl (Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,Or.inr ⟨file,low,short⟩⟩)⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨rfl,rfl,condition⟩))

theorem sufficient {rs : Square} (apart : ((3 : Fin 8),1) ≠ rs) (region : Region rs) :
    KRKTwelveGeometry.Clear (3,1) rs (1,1) := by
  by_cases fresh : rs.1.val = 1 ∧ rs.2.val = 5
  · exact (KRKTwelveInnerFileOne.clear_iff apart rfl rfl fresh.1).mpr ⟨by omega,by omega⟩
  exact KRKTwelveInner.ten_clear_subset apart (by decide) (KRKTenInner.sufficient (old_of_not_fresh region fresh))

theorem clear_iff {rs : Square} (apart : ((3 : Fin 8),1) ≠ rs) :
    KRKTwelveGeometry.Clear (3,1) rs (1,1) ↔ Region rs := ⟨necessary apart,sufficient apart⟩

theorem kernel_twelve_iff {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,1) rs (1,1)) (turn : q.turn = σ.opp) : MateWithin σ 12 q ↔ Region rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans (clear_iff material.1)

theorem kernel_exact_twelve {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,1) rs (1,1)) (turn : q.turn = σ.opp) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ rs = ((1 : Fin 8),5) := by
  constructor
  · rintro ⟨twelve,notEleven⟩
    have region := (kernel_twelve_iff material turn).mp twelve
    by_cases fresh : rs = ((1 : Fin 8),5)
    · exact fresh
    have notNew : ¬(rs.1.val = 1 ∧ rs.2.val = 5) := by
      rintro ⟨x,y⟩
      exact fresh (Prod.ext (Fin.ext x) (Fin.ext y))
    have old := old_of_not_fresh region notNew
    have ten := (KRKTenInner.kernel_ten_iff material turn (by decide)).mpr old
    exact False.elim (notEleven (mateWithin_mono ten (by decide)))
  · intro equal
    rw [equal] at material
    exact KRKTwelveInnerFileOne.kernel_exact_twelve material turn

end EndgameChess.Rules.KRKTwelveInnerSide
