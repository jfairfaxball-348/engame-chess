import EndgameChess.Rules.KRKTwelveInnerUpperFive

namespace EndgameChess.Rules.KRKTwelveInnerExact
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Low (sk rs : Square) : Prop := sk.1.val = 3 ∧ sk.2.val = 0 ∧ rs.2.val = 2 ∧ 3 ≤ rs.1.val

def Side (sk rs : Square) : Prop := sk.1.val = 3 ∧ sk.2.val = 1 ∧ KRKTwelveInnerSide.Region rs

def High (sk rs : Square) : Prop := sk.1.val = 3 ∧ sk.2.val = 2 ∧ KRKTwelveInnerHighExact.Region rs

def Diagonal (sk rs : Square) : Prop := sk.1.val = 3 ∧ sk.2.val = 3 ∧ KRKTwelveInnerDiagonalExact.Region rs

def Outer (sk rs : Square) : Prop := sk.1.val = 4 ∧ (sk.2.val = 1 ∨ sk.2.val = 2) ∧ rs = ((2 : Fin 8),3)

def UpperFive (sk rs : Square) : Prop := sk = ((1 : Fin 8),5) ∧ rs = ((2 : Fin 8),4)

def Horizontal (sk rs : Square) : Prop :=
  Low sk rs ∨ Side sk rs ∨ High sk rs ∨ Diagonal sk rs ∨ Outer sk rs ∨
    KRKTwelveInnerUpperFour.Region sk rs ∨ UpperFive sk rs

def Region (sk rs : Square) : Prop := Horizontal sk rs ∨ Horizontal (symSwap.f sk) (symSwap.f rs)

private theorem three_necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (ys : sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3) (clear : KRKTwelveGeometry.Clear sk rs (1,1)) :
    Horizontal sk rs := by
  rcases ys with one | two | three
  · have equal : sk = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext one)
    rw [equal] at apart clear ⊢
    exact Or.inr (Or.inl ⟨rfl,rfl,KRKTwelveInnerSide.necessary apart clear⟩)
  · have equal : sk = ((3 : Fin 8),2) := Prod.ext (Fin.ext sx) (Fin.ext two)
    rw [equal] at apart clear ⊢
    exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,KRKTwelveInnerHighExact.necessary apart clear⟩))
  · have equal : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext three)
    rw [equal] at apart clear ⊢
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,KRKTwelveInnerDiagonalExact.necessary apart clear⟩)))

private theorem horizontal_prison_necessary {sk rs : Square} (apart : sk ≠ rs)
    (clear : KRKTwelveGeometry.Clear sk rs (1,1)) (shape : KRKTwelveInner.HorizontalPrison sk rs) :
    Horizontal sk rs := by
  rcases shape with ⟨sx,low,high⟩ | ⟨sx,low,high,rx,ry⟩ | ⟨sy,sx,rx,_⟩
  · exact three_necessary apart sx (by omega) clear
  · have kingEq : sk = ((4 : Fin 8),sk.2) := Prod.ext (Fin.ext sx) rfl
    have rookEq : rs = ((2 : Fin 8),3) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    have source := clear
    rw [kingEq,rookEq] at source
    have choice := (KRKTwelveInnerOuter.clear_iff ⟨low,high⟩).mp source
    have ys : sk.2.val = 1 ∨ sk.2.val = 2 := by
      rcases choice with one | two
      · exact Or.inl (congrArg Fin.val one)
      · exact Or.inr (congrArg Fin.val two)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sx,ys,rookEq⟩))))
  · rcases sy with four | five
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (KRKTwelveInnerUpperFour.necessary apart sx four rx clear))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((KRKTwelveInnerUpperFive.clear_iff apart sx five rx).mp clear))))))

private theorem row_necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val ≤ 2) (ry : rs.2.val = 2) (clear : KRKTwelveGeometry.Clear sk rs (1,1)) :
    Horizontal sk rs := by
  by_cases zero : sk.2.val = 0
  · have width : 3 ≤ rs.1.val := by
      have safe := clear.1
      dsimp [SafeRook,dInf,absDiff] at safe
      omega
    exact Or.inl ⟨sx,zero,ry,width⟩
  · exact three_necessary apart sx (by omega) clear

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1))
    (clear : KRKTwelveGeometry.Clear sk rs (1,1)) : Region sk rs := by
  have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symSwap) apart clear
  have mappedApart := (Frame.ofSym symSwap).ne_iff.mpr apart
  rcases KRKTwelveInner.prison apart far clear with horizontal | vertical | corner
  · exact Or.inl (horizontal_prison_necessary apart clear horizontal)
  · exact Or.inr (horizontal_prison_necessary mappedApart mapped vertical)
  · rcases corner with ⟨sx,sy,ry⟩ | ⟨sy,sx,rx⟩ | ⟨sx,sy,_⟩ | ⟨sy,sx,_⟩ | ⟨sx,sy,_,_⟩
    · exact Or.inl (row_necessary apart sx sy ry clear)
    · exact Or.inr (row_necessary mappedApart sy sx rx mapped)
    · exact Or.inl (three_necessary apart sx (by omega) clear)
    · exact Or.inr (three_necessary mappedApart sy (by dsimp [Frame.ofSym,symSwap]; omega) mapped)
    · exact Or.inl (three_necessary apart sx (Or.inr (Or.inr sy)) clear)

private theorem horizontal_sufficient {sk rs : Square} (apart : sk ≠ rs) (horizontal : Horizontal sk rs) :
    KRKTwelveGeometry.Clear sk rs (1,1) := by
  rcases horizontal with low | side | high | diagonal | outer | four | five
  · obtain ⟨sx,sy,ry,rx⟩ := low
    have old : KRKTenInner.Region sk rs := Or.inl (Or.inl ⟨sx,Or.inl ⟨sy,ry,rx⟩⟩)
    have far : 2 ≤ dInf sk (1,1) := by dsimp [dInf,absDiff]; omega
    exact KRKTwelveInner.ten_clear_subset apart far (KRKTenInner.sufficient old)
  · obtain ⟨sx,sy,region⟩ := side
    have equal : sk = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    rw [equal] at apart ⊢
    exact KRKTwelveInnerSide.sufficient apart region
  · obtain ⟨sx,sy,region⟩ := high
    have equal : sk = ((3 : Fin 8),2) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    rw [equal] at apart ⊢
    exact KRKTwelveInnerHighExact.sufficient apart region
  · obtain ⟨sx,sy,region⟩ := diagonal
    have equal : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    rw [equal]
    exact KRKTwelveInnerDiagonalExact.sufficient region
  · obtain ⟨sx,ys,rookEq⟩ := outer
    have kingEq : sk = ((4 : Fin 8),sk.2) := Prod.ext (Fin.ext sx) rfl
    rw [kingEq,rookEq]
    apply KRKTwelveInnerOuter.low_clear
    rcases ys with one | two
    · exact Or.inl (Fin.ext one)
    · exact Or.inr (Fin.ext two)
  · exact KRKTwelveInnerUpperFour.sufficient four
  · obtain ⟨rfl,rfl⟩ := five
    exact KRKTwelveInnerUpperFive.clear

theorem sufficient {sk rs : Square} (apart : sk ≠ rs) (region : Region sk rs) :
    KRKTwelveGeometry.Clear sk rs (1,1) := by
  rcases region with horizontal | vertical
  · exact horizontal_sufficient apart horizontal
  · have source := horizontal_sufficient ((Frame.ofSym symSwap).ne_iff.mpr apart) vertical
    have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symSwap)
      ((Frame.ofSym symSwap).ne_iff.mpr apart) source
    simpa only [Frame.ofSym,symSwap.invol,show symSwap.f ((1 : Fin 8),1) = ((1 : Fin 8),1) from rfl] using mapped

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,1)) :
    KRKTwelveGeometry.Clear sk rs (1,1) ↔ Region sk rs := ⟨necessary apart far,sufficient apart⟩

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1)) :
    MateWithin σ 12 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans (clear_iff material.1 far)

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,1)) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region sk rs ∧ ¬KRKTenInner.Region sk rs := by
  constructor
  · rintro ⟨twelve,notEleven⟩
    refine ⟨(kernel_twelve_iff material turn far).mp twelve,?_⟩
    intro old
    exact notEleven (mateWithin_mono ((KRKTenInner.kernel_ten_iff material turn far).mpr old) (by decide))
  · rintro ⟨region,notOld⟩
    exact ⟨(kernel_twelve_iff material turn far).mpr region,fun eleven =>
      notOld ((KRKTenInner.kernel_ten_iff material turn far).mp (KRKTenGeometry.weak_eleven_ten material turn eleven))⟩

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),1))
    (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKTwelveGeometry.Clear sk rs wk ↔ Region (g.f sk) (g.f rs) := by
  constructor
  · intro clear
    have mapped := KRKTwelveGeometry.frame_map g apart clear
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    rw [target] at mapped mappedFar
    exact necessary (g.ne_iff.mpr apart) mappedFar mapped
  · intro region
    have mapped := sufficient (g.ne_iff.mpr apart) region
    have shaped : KRKTwelveGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKTwelveGeometry.frame_map g.inverse (g.ne_iff.mpr apart) shaped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKTwelveInnerExact
