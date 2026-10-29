import EndgameChess.Rules.KRKCentral.PrepPair

/-! KRK01: executable, frozen-geometry centralisation action, NOT a policy. -/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

/-- Concrete king target of the centralising one-pair lemma.
This function has no classical witness and can be directly translated. -/
def prepDestination (sk rs : Square) : Square :=
  let x : Fin 8 :=
    if h : sk.1.val < 3 then ⟨sk.1.val + 1, by omega⟩
    else if h : 4 < sk.1.val then ⟨sk.1.val - 1, by omega⟩
    else sk.1
  let z : Fin 8 :=
    if h : sk.2.val + 1 < rs.2.val then ⟨sk.2.val + 1, by omega⟩
    else sk.2
  (x, z)

/-- The exact executable king destination reduces prepDistance by one,
and ALL actual legal weak replies retain the rook wall. -/
theorem prepDestination_sound {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val)
    (ht : 0 < prepDistance rs.2.val sk)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨prepDestination sk rs, rs, wk, false⟩ ∧
      prepDistance rs.2.val (prepDestination sk rs) + 1 =
        prepDistance rs.2.val sk ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨prepDestination sk rs, rs, t, true⟩ ∧
          rs.2.val < t.2.val := by
  let x : Fin 8 :=
    if h : sk.1.val < 3 then ⟨sk.1.val + 1, by omega⟩
    else if h : 4 < sk.1.val then ⟨sk.1.val - 1, by omega⟩
    else sk.1
  let z : Fin 8 :=
    if h : sk.2.val + 1 < rs.2.val then ⟨sk.2.val + 1, by omega⟩
    else sk.2
  let su : Square := (x, z)
  have target : su = prepDestination sk rs := rfl
  have hxgeom : absDiff sk.1.val x.val ≤ 1 ∧
      centreDistance x.val = centreDistance sk.1.val - 1 ∧
      (centreDistance sk.1.val ≠ 0 → absDiff sk.1.val x.val = 1) := by
    by_cases hx : sk.1.val < 3 <;> by_cases hx4 : 4 < sk.1.val <;>
      simp [x, hx, hx4, centreDistance, absDiff] <;> (try split) <;>
      (try split) <;> omega
  have hzgeom : absDiff sk.2.val z.val ≤ 1 ∧ z.val < rs.2.val ∧
      rs.2.val - (z.val + 1) = (rs.2.val - (sk.2.val + 1)) - 1 ∧
      (rs.2.val - (sk.2.val + 1) ≠ 0 → absDiff sk.2.val z.val = 1) := by
    by_cases hy : sk.2.val + 1 < rs.2.val <;>
      simp [z, hy, absDiff] <;> omega
  have geom : dInf sk su = 1 ∧ su.2.val < rs.2.val ∧
      prepDistance rs.2.val su + 1 = prepDistance rs.2.val sk := by
    change max (absDiff sk.1.val x.val) (absDiff sk.2.val z.val) = 1 ∧
      z.val < rs.2.val ∧ prepDistance rs.2.val su + 1 =
        prepDistance rs.2.val sk
    simp only [prepDistance, su] at *
    omega
  obtain ⟨c, hl, hm, hne, hall⟩ :=
    king_below_pair hq geom.1 geom.2.1 hw hf
  rw [target] at hm
  rw [target] at geom
  refine ⟨c, hl, hm, geom.2.2, hne, ?_⟩
  intro v hv
  obtain ⟨t, hmt, hty, _⟩ := hall v hv
  rw [target] at hmt
  exact ⟨t, hmt, hty⟩

end EndgameChess.Rules.KRKExecutable
