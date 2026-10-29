import EndgameChess.Rules.KRKSevenCorner

namespace EndgameChess.Rules.KRKEightEdge
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Complete seven-ply destination catalogue for the five edge neighbours
and inward-corner exceptions of a canonical edge root. -/
def SevenTest (sk rs t : Square) : Prop :=
  (t = ((0 : Fin 8),0) ∧ KRKSevenCorner.Seven sk rs) ∨
  (t = ((1 : Fin 8),0) ∧ KRKSevenNear.Seven sk rs) ∨
  (t = ((2 : Fin 8),0) ∧ KRKSevenSecond.Seven sk rs) ∨
  ((t = ((3 : Fin 8),0) ∨ t = ((4 : Fin 8),0)) ∧ KRKFiveMiddle.BottomFive sk rs t) ∨
  (t = ((0 : Fin 8),1) ∧ KRKSevenNear.Seven (symSwap.f sk) (symSwap.f rs)) ∨
  (t = ((1 : Fin 8),1) ∧ KRKSevenInner.Seven sk rs)

private theorem west_clear_iff {sk rs : Square} (apart : sk ≠ rs) (notKing : sk ≠ ((0 : Fin 8),1))
    (notRook : rs ≠ ((0 : Fin 8),1)) (far : 2 ≤ dInf sk (0,1))
    (notCheck : ¬RookSees rs (0,1) sk (0,1)) :
    KRKSevenGeometry.Clear sk rs (0,1) ↔ KRKSevenNear.Seven (symSwap.f sk) (symSwap.f rs) := by
  let g := Frame.ofSym symSwap
  constructor
  · intro clear
    have mapped := KRKSevenReach.frame_map g apart notKing notRook far notCheck clear
    exact (KRKSevenNear.clear_iff (g.ne_iff.mpr apart) (g.ne_iff.mpr notRook)
      (fun h => notCheck ((g.sees _ _ _ _).mp h))).mp mapped
  · intro seven
    have mapped := (KRKSevenNear.clear_iff (g.ne_iff.mpr apart) (g.ne_iff.mpr notRook)
      (fun h => notCheck ((g.sees _ _ _ _).mp h))).mpr seven
    have back := KRKSevenReach.frame_map g (g.ne_iff.mpr apart) (g.ne_iff.mpr notKing)
      (g.ne_iff.mpr notRook) (by rw [g.distance]; exact far)
      (fun h => notCheck ((g.sees _ _ _ _).mp h)) mapped
    simpa only [g,Frame.ofSym,symSwap.invol] using back

theorem seven_test_iff {sk rs t : Square} (apart : sk ≠ rs) (notKing : sk ≠ t) (notRook : rs ≠ t)
    (far : 2 ≤ dInf sk t) (notCheck : ¬RookSees rs t sk t)
    (x : t.1.val ≤ 4) (y : t.2.val ≤ 1) :
    KRKSevenGeometry.Clear sk rs t ↔ SevenTest sk rs t := by
  have cases : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
      t = ((3 : Fin 8),0) ∨ t = ((4 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨
      t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) ∨ t = ((3 : Fin 8),1) ∨ t = ((4 : Fin 8),1) := by
    simp only [square_eq_iff,Fin.ext_iff]
    dsimp
    omega
  have innerImpossible : ∀ {t : Square}, t.2.val = 1 → 2 ≤ t.1.val → t.1.val ≤ 4 →
      ¬KRKSevenGeometry.Clear sk rs t := by
    intro t ty low high clear
    rcases KRKSevenReach.weak_domain clear with edge | inner
    · dsimp [KRKEdgeDepth.depth] at edge; omega
    · dsimp [KRKSixInterior.InnerCorner] at inner; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SevenTest] using KRKSevenCorner.clear_iff apart notKing notRook far notCheck
  · simpa [SevenTest] using KRKSevenNear.clear_iff apart notRook notCheck
  · simpa [SevenTest] using KRKSevenSecond.clear_iff apart notRook notCheck
  · simpa [SevenTest] using KRKSevenMiddle.bottom_clear_iff rfl (by decide) (by decide) apart notKing notRook far notCheck
  · simpa [SevenTest] using KRKSevenMiddle.bottom_clear_iff rfl (by decide) (by decide) apart notKing notRook far notCheck
  · simpa [SevenTest] using west_clear_iff apart notKing notRook far notCheck
  · simpa [SevenTest] using KRKSevenInner.clear_iff apart notKing notRook far notCheck
  · simp only [SevenTest]; simp; exact innerImpossible rfl (by decide) (by decide)
  · simp only [SevenTest]; simp; exact innerImpossible rfl (by decide) (by decide)
  · simp only [SevenTest]; simp; exact innerImpossible rfl (by decide) (by decide)

def left (wk : Square) : Fin 8 := ⟨wk.1.val - 1,by have := wk.1.isLt; omega⟩
def right (wk : Square) : Fin 8 := ⟨min 7 (wk.1.val + 1),by omega⟩

inductive Reply where
  | west | east | northWest | north | northEast

def destination (wk : Square) : Reply → Square
  | .west => (left wk,0)
  | .east => (right wk,0)
  | .northWest => (left wk,1)
  | .north => (wk.1,1)
  | .northEast => (right wk,1)

theorem reply_point {sk rs wk t : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3)
    (guard : KRKCornerWeakBand.Guard sk rs wk t) : ∃ i, t = destination wk i := by
  have distance := guard.1
  dsimp [dInf,absDiff] at distance
  have choices :
      (t.1.val = wk.1.val - 1 ∧ t.2.val = 0) ∨
      (t.1.val = wk.1.val + 1 ∧ t.2.val = 0) ∨
      (t.1.val = wk.1.val - 1 ∧ t.2.val = 1) ∨
      (t.1.val = wk.1.val ∧ t.2.val = 1) ∨
      (t.1.val = wk.1.val + 1 ∧ t.2.val = 1) := by omega
  rcases choices with ⟨tx,ty⟩ | ⟨tx,ty⟩ | ⟨tx,ty⟩ | ⟨tx,ty⟩ | ⟨tx,ty⟩
  · exact ⟨.west,Prod.ext (Fin.ext tx) (Fin.ext ty)⟩
  · refine ⟨.east,Prod.ext (Fin.ext ?_) (Fin.ext ty)⟩
    dsimp [destination,right]; omega
  · exact ⟨.northWest,Prod.ext (Fin.ext tx) (Fin.ext ty)⟩
  · exact ⟨.north,Prod.ext (Fin.ext tx) (Fin.ext ty)⟩
  · refine ⟨.northEast,Prod.ext (Fin.ext ?_) (Fin.ext ty)⟩
    dsimp [destination,right]; omega

/-- Five fixed geometric reply tests; all subsequent regions are evaluated
point/rook inequalities, with no winning predicate or game recurrence. -/
def Region (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧
    (∃ i : Reply, KRKCornerWeakBand.Guard sk rs wk (destination wk i)) ∧
    ∀ i : Reply, KRKCornerWeakBand.Guard sk rs wk (destination wk i) →
      SevenTest sk rs (destination wk i)

theorem clear_iff {sk rs wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3)
    (apart : sk ≠ rs) : KRKEightGeometry.Clear sk rs wk ↔ Region sk rs wk := by
  have bounded : ∀ i : Reply, (destination wk i).1.val ≤ 4 ∧ (destination wk i).2.val ≤ 1 := by
    intro i
    cases i <;> dsimp [destination,left,right] <;> omega
  have test : ∀ {t : Square}, KRKCornerWeakBand.Guard sk rs wk t → t.1.val ≤ 4 → t.2.val ≤ 1 →
      (KRKSevenGeometry.Clear sk rs t ↔ SevenTest sk rs t) := by
    intro t guard x y
    exact seven_test_iff apart (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
      guard.2.1.symm guard.2.2.1 guard.2.2.2 x y
  constructor
  · rintro ⟨safe,⟨t,guard⟩,every⟩
    obtain ⟨i,rfl⟩ := reply_point rank high guard
    refine ⟨safe,⟨i,guard⟩,?_⟩
    intro j guard
    exact (test guard (bounded j).1 (bounded j).2).mp (every _ guard)
  · rintro ⟨safe,⟨i,guard⟩,every⟩
    refine ⟨safe,⟨_,guard⟩,?_⟩
    intro t guard
    obtain ⟨j,rfl⟩ := reply_point rank high guard
    exact (test guard (bounded j).1 (bounded j).2).mpr (every j guard)

theorem kernel_eight_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) (notMate : ¬MatedK q) :
    MateWithin σ 8 q ↔ Region sk rs wk :=
  (KRKEightGeometry.kernel_eight_iff material turn notMate).trans (clear_iff rank high material.1)

end EndgameChess.Rules.KRKEightEdge
