import EndgameChess.Rules.KRKNineEdge

namespace EndgameChess.Rules.KRKTenEdge
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

/-- Fixed nine-ply destination catalogue for a canonical edge root. The
edge alternatives are explicit forty-point/ray intersection formulas;
the inward/near-strip alternatives have evaluated rook inequalities. -/
def NineTest (sk rs t : Square) : Prop :=
  (t = ((0 : Fin 8),0) ∧ KRKNineEdge.Nine sk rs (0,0)) ∨
  (t = ((1 : Fin 8),0) ∧ KRKNineEdge.Nine sk rs (1,0)) ∨
  (t = ((2 : Fin 8),0) ∧ KRKNineEdge.Nine sk rs (2,0)) ∨
  (t = ((3 : Fin 8),0) ∧ KRKNineEdge.Nine sk rs (3,0)) ∨
  (t = ((4 : Fin 8),0) ∧ KRKNineEdge.Nine (symX.f sk) (symX.f rs) (3,0)) ∨
  (t = ((0 : Fin 8),1) ∧ KRKNineEdge.Nine (symSwap.f sk) (symSwap.f rs) (1,0)) ∨
  (t = ((1 : Fin 8),1) ∧ KRKNineInner.Nine sk rs) ∨
  (t = ((2 : Fin 8),1) ∧ KRKNineNearStrip.Nine (symSwap.f sk) (symSwap.f rs))

private theorem mapped_clear_iff (g : Frame) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) :
    KRKNineGeometry.Clear sk rs wk ↔ KRKNineGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by
  constructor
  · exact KRKNineGeometry.frame_map g distinct notKing notRook far notCheck
  · intro clear
    have back := KRKNineGeometry.frame_map g.inverse (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing)
      (g.ne_iff.mpr notRook) (by rw [g.distance]; exact far)
      (fun h => notCheck ((g.sees _ _ _ _).mp h)) clear
    simpa only [Frame.inverse,g.left_inv] using back

private theorem middle_no_nine {sk rs t : Square} (distinct : sk ≠ rs) (notKing : sk ≠ t)
    (notRook : rs ≠ t) (far : 2 ≤ dInf sk t) (notCheck : ¬RookSees rs t sk t)
    (middle : KRKEightCentralStrip.MiddleStrip t) : ¬KRKNineGeometry.Clear sk rs t := by
  intro clear
  let q := krkPos .white sk rs t .white
  have material : IsKRK q .white sk rs t := ⟨distinct,notKing,notRook,rfl⟩
  have nine := KRKNineGeometry.sufficient material rfl far notCheck clear
  exact KRKEightCentralStripHolding.strong_no_ten material rfl middle (mateWithin_mono nine (by decide))

theorem nine_test_iff {sk rs t : Square} (distinct : sk ≠ rs) (notKing : sk ≠ t) (notRook : rs ≠ t)
    (far : 2 ≤ dInf sk t) (notCheck : ¬RookSees rs t sk t) (x : t.1.val ≤ 4) (y : t.2.val ≤ 1) :
    KRKNineGeometry.Clear sk rs t ↔ NineTest sk rs t := by
  have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
      t = ((3 : Fin 8),0) ∨ t = ((4 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨
      t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) ∨ t = ((3 : Fin 8),1) ∨ t = ((4 : Fin 8),1) := by
    simp only [square_eq_iff,Fin.ext_iff]
    dsimp
    omega
  rcases targets with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [NineTest] using (KRKNineEdge.clear_iff (wk := ((0 : Fin 8),0)) rfl (by decide))
  · simpa [NineTest] using (KRKNineEdge.clear_iff (wk := ((1 : Fin 8),0)) rfl (by decide))
  · simpa [NineTest] using (KRKNineEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide))
  · simpa [NineTest] using (KRKNineEdge.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide))
  · have mapped := mapped_clear_iff (Frame.ofSym symX) distinct notKing notRook far notCheck
    have evaluated := KRKNineEdge.clear_iff (sk := symX.f sk) (rs := symX.f rs) (wk := ((3 : Fin 8),0)) rfl (by decide)
    simpa [NineTest] using mapped.trans evaluated
  · have mapped := mapped_clear_iff (Frame.ofSym symSwap) distinct notKing notRook far notCheck
    have evaluated := KRKNineEdge.clear_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := ((1 : Fin 8),0)) rfl (by decide)
    simpa [NineTest] using mapped.trans evaluated
  · simpa [NineTest] using KRKNineInner.clear_iff distinct notKing notRook far notCheck
  · have mapped := mapped_clear_iff (Frame.ofSym symSwap) distinct notKing notRook far notCheck
    have evaluated := KRKNineNearStrip.clear_iff ((Frame.ofSym symSwap).ne_iff.mpr distinct)
      ((Frame.ofSym symSwap).ne_iff.mpr notKing) ((Frame.ofSym symSwap).ne_iff.mpr notRook)
      (by change 2 ≤ dInf (symSwap.f sk) (symSwap.f ((2 : Fin 8),1)); rw [symSwap.dInf_eq]; exact far)
      (fun h => notCheck ((symSwap.sees_iff _ _ _ _).mp h))
    simpa [NineTest,Frame.ofSym] using mapped.trans evaluated
  · simp only [NineTest]; simp
    exact middle_no_nine distinct notKing notRook far notCheck (Or.inr ⟨Or.inl rfl,by decide,by decide⟩)
  · simp only [NineTest]; simp
    exact middle_no_nine distinct notKing notRook far notCheck (Or.inr ⟨Or.inl rfl,by decide,by decide⟩)

/-- Five compass destinations with closed geometric point/ray tests. -/
def Region (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧
    (∃ i : KRKEightEdge.Reply, KRKCornerWeakBand.Guard sk rs wk (KRKEightEdge.destination wk i)) ∧
    ∀ i : KRKEightEdge.Reply, KRKCornerWeakBand.Guard sk rs wk (KRKEightEdge.destination wk i) →
      NineTest sk rs (KRKEightEdge.destination wk i)

theorem clear_iff {sk rs wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) (distinct : sk ≠ rs) :
    KRKTenGeometry.Clear sk rs wk ↔ Region sk rs wk := by
  have bounded : ∀ i : KRKEightEdge.Reply,
      (KRKEightEdge.destination wk i).1.val ≤ 4 ∧ (KRKEightEdge.destination wk i).2.val ≤ 1 := by
    intro i
    cases i <;> dsimp [KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right] <;> omega
  have test : ∀ {t : Square}, KRKCornerWeakBand.Guard sk rs wk t → t.1.val ≤ 4 → t.2.val ≤ 1 →
      (KRKNineGeometry.Clear sk rs t ↔ NineTest sk rs t) := by
    intro t guard x y
    exact nine_test_iff distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
      guard.2.1.symm guard.2.2.1 guard.2.2.2 x y
  constructor
  · rintro ⟨safe,⟨t,guard⟩,every⟩
    obtain ⟨i,rfl⟩ := KRKEightEdge.reply_point rank high guard
    refine ⟨safe,⟨i,guard⟩,?_⟩
    intro j guard
    exact (test guard (bounded j).1 (bounded j).2).mp (every _ guard)
  · rintro ⟨safe,⟨i,guard⟩,every⟩
    refine ⟨safe,⟨_,guard⟩,?_⟩
    intro t guard
    obtain ⟨j,rfl⟩ := KRKEightEdge.reply_point rank high guard
    exact (test guard (bounded j).1 (bounded j).2).mpr (every j guard)

theorem kernel_ten_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (rank : wk.2.val = 0)
    (high : wk.1.val ≤ 3) (notMate : ¬MatedK q) : MateWithin σ 10 q ↔ Region sk rs wk :=
  (KRKTenGeometry.kernel_ten_iff material turn notMate).trans (clear_iff rank high material.1)

end EndgameChess.Rules.KRKTenEdge
