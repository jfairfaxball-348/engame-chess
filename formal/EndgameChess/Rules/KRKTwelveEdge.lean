import EndgameChess.Rules.KRKElevenEdge

namespace EndgameChess.Rules.KRKTwelveEdge
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

/-- Fixed eleven-ply destination catalogue for a canonical edge root. The
edge alternatives are explicit forty-eight-point/ray intersection formulas;
the inward/near-strip alternatives have evaluated rook inequalities. -/
def ElevenTest (sk rs t : Square) : Prop :=
  (t = ((0 : Fin 8),0) ∧ KRKElevenEdge.Eleven sk rs (0,0)) ∨
  (t = ((1 : Fin 8),0) ∧ KRKElevenEdge.Eleven sk rs (1,0)) ∨
  (t = ((2 : Fin 8),0) ∧ KRKElevenEdge.Eleven sk rs (2,0)) ∨
  (t = ((3 : Fin 8),0) ∧ KRKElevenEdge.Eleven sk rs (3,0)) ∨
  (t = ((4 : Fin 8),0) ∧ KRKElevenEdge.Eleven (symX.f sk) (symX.f rs) (3,0)) ∨
  (t = ((0 : Fin 8),1) ∧ KRKElevenEdge.Eleven (symSwap.f sk) (symSwap.f rs) (1,0)) ∨
  (t = ((1 : Fin 8),1) ∧ KRKElevenInner.Eleven sk rs) ∨
  (t = ((2 : Fin 8),1) ∧ KRKElevenNearStrip.Eleven (symSwap.f sk) (symSwap.f rs))

private theorem mapped_clear_iff (g : Frame) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk)
    (notCheck : ¬RookSees rs wk sk wk) :
    KRKElevenGeometry.Clear sk rs wk ↔ KRKElevenGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by
  constructor
  · exact KRKElevenGeometry.frame_map g distinct notKing notRook far notCheck
  · intro clear
    have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing)
      (g.ne_iff.mpr notRook) (by rw [g.distance]; exact far)
      (fun h => notCheck ((g.sees _ _ _ _).mp h)) clear
    simpa only [Frame.inverse,g.left_inv] using back

private theorem middle_no_eleven {sk rs t : Square} (distinct : sk ≠ rs) (notKing : sk ≠ t)
    (notRook : rs ≠ t) (far : 2 ≤ dInf sk t) (notCheck : ¬RookSees rs t sk t)
    (middle : KRKEightCentralStrip.MiddleStrip t) : ¬KRKElevenGeometry.Clear sk rs t := by
  intro clear
  let q := krkPos .white sk rs t .white
  have material : IsKRK q .white sk rs t := ⟨distinct,notKing,notRook,rfl⟩
  have eleven := KRKElevenGeometry.sufficient material rfl far notCheck clear
  exact KRKTenCentralStripHolding.strong_no_twelve material rfl middle (mateWithin_mono eleven (by decide))

theorem eleven_test_iff {sk rs t : Square} (distinct : sk ≠ rs) (notKing : sk ≠ t) (notRook : rs ≠ t)
    (far : 2 ≤ dInf sk t) (notCheck : ¬RookSees rs t sk t) (x : t.1.val ≤ 4) (y : t.2.val ≤ 1) :
    KRKElevenGeometry.Clear sk rs t ↔ ElevenTest sk rs t := by
  have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
      t = ((3 : Fin 8),0) ∨ t = ((4 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨
      t = ((1 : Fin 8),1) ∨ t = ((2 : Fin 8),1) ∨ t = ((3 : Fin 8),1) ∨ t = ((4 : Fin 8),1) := by
    simp only [square_eq_iff,Fin.ext_iff]
    dsimp
    omega
  rcases targets with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ElevenTest] using (KRKElevenEdge.clear_iff (wk := ((0 : Fin 8),0)) rfl (by decide))
  · simpa [ElevenTest] using (KRKElevenEdge.clear_iff (wk := ((1 : Fin 8),0)) rfl (by decide))
  · simpa [ElevenTest] using (KRKElevenEdge.clear_iff (wk := ((2 : Fin 8),0)) rfl (by decide))
  · simpa [ElevenTest] using (KRKElevenEdge.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide))
  · have mapped := mapped_clear_iff (Frame.ofSym symX) distinct notKing notRook far notCheck
    have evaluated := KRKElevenEdge.clear_iff (sk := symX.f sk) (rs := symX.f rs) (wk := ((3 : Fin 8),0)) rfl (by decide)
    simpa [ElevenTest] using mapped.trans evaluated
  · have mapped := mapped_clear_iff (Frame.ofSym symSwap) distinct notKing notRook far notCheck
    have evaluated := KRKElevenEdge.clear_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := ((1 : Fin 8),0)) rfl (by decide)
    simpa [ElevenTest] using mapped.trans evaluated
  · simpa [ElevenTest] using KRKElevenInner.clear_iff distinct notKing notRook far notCheck
  · have mapped := mapped_clear_iff (Frame.ofSym symSwap) distinct notKing notRook far notCheck
    have evaluated := KRKElevenNearStrip.clear_iff ((Frame.ofSym symSwap).ne_iff.mpr distinct)
      ((Frame.ofSym symSwap).ne_iff.mpr notRook)
    simpa [ElevenTest,Frame.ofSym] using mapped.trans evaluated
  · simp only [ElevenTest]; simp
    exact middle_no_eleven distinct notKing notRook far notCheck (Or.inr ⟨Or.inl rfl,by decide,by decide⟩)
  · simp only [ElevenTest]; simp
    exact middle_no_eleven distinct notKing notRook far notCheck (Or.inr ⟨Or.inl rfl,by decide,by decide⟩)

/-- Five compass destinations with closed geometric point/ray tests. -/
def Region (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧
    (∃ i : KRKEightEdge.Reply, KRKCornerWeakBand.Guard sk rs wk (KRKEightEdge.destination wk i)) ∧
    ∀ i : KRKEightEdge.Reply, KRKCornerWeakBand.Guard sk rs wk (KRKEightEdge.destination wk i) →
      ElevenTest sk rs (KRKEightEdge.destination wk i)

theorem clear_iff {sk rs wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) (distinct : sk ≠ rs) :
    KRKTwelveGeometry.Clear sk rs wk ↔ Region sk rs wk := by
  have bounded : ∀ i : KRKEightEdge.Reply,
      (KRKEightEdge.destination wk i).1.val ≤ 4 ∧ (KRKEightEdge.destination wk i).2.val ≤ 1 := by
    intro i
    cases i <;> dsimp [KRKEightEdge.destination,KRKEightEdge.left,KRKEightEdge.right] <;> omega
  have test : ∀ {t : Square}, KRKCornerWeakBand.Guard sk rs wk t → t.1.val ≤ 4 → t.2.val ≤ 1 →
      (KRKElevenGeometry.Clear sk rs t ↔ ElevenTest sk rs t) := by
    intro t guard x y
    exact eleven_test_iff distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
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

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (rank : wk.2.val = 0)
    (high : wk.1.val ≤ 3) (notMate : ¬MatedK q) : MateWithin σ 12 q ↔ Region sk rs wk :=
  (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans (clear_iff rank high material.1)

end EndgameChess.Rules.KRKTwelveEdge
