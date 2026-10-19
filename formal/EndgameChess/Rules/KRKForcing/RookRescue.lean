import EndgameChess.Rules.KRKForcing.RankAdvance

/-! S028: a hanging barrier rook is rescued before the next weak turn. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

theorem barrier_horizontal_reply_exists {sk rs wk : Square}
    (hgap : sk.2.val + 2 ≤ wk.2.val) (hw : rs.2.val < wk.2.val)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := by
  by_cases hx : wk.1.val < 7
  · let t : Square := (⟨wk.1.val + 1, by omega⟩, wk.2)
    refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩ <;> dsimp [t] <;>
      simp only [RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega
  · let t : Square := (⟨wk.1.val - 1, by omega⟩, wk.2)
    refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩ <;> dsimp [t] <;>
      simp only [RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega

/-- When a barrier rook is hanging, choose the far file and cover every reply.
No intermediate weak move is permitted before the rescue. -/
theorem krk_barrier_rook_rescue {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val)
    (hunsafe : dInf rs wk < 2) :
    ∃ nr c, nr.2 = rs.2 ∧ 4 ≤ absDiff nr.1.val wk.1.val ∧ Legal q c ∧
      Matches c σ ⟨sk, nr, wk, false⟩ ∧ (∃ r, Legal c r) ∧
      ∀ r, Legal c r → ∃ t, Matches r σ ⟨sk, nr, t, true⟩ ∧
        DistantBarrier sk nr t := by
  let nx : Fin 8 := if 4 ≤ wk.1.val then 0 else 7
  let nr : Square := (nx, rs.2)
  have hfar : 4 ≤ absDiff nr.1.val wk.1.val := by
    dsimp [nr, nx]; split <;> simp only [absDiff] <;> omega
  have hny : nr.2 = rs.2 := rfl
  have hstep : StepM ⟨sk, rs, wk, true⟩ ⟨sk, nr, wk, false⟩ := by
    refine StepM.rook ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;>
      dsimp only [nr] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hstep
  have hgap : sk.2.val + 2 ≤ wk.2.val := by omega
  have hwy : nr.2.val < wk.2.val := hw
  obtain ⟨t, ht⟩ := barrier_horizontal_reply_exists hgap hwy (by omega)
  obtain ⟨r, hr, _⟩ := step_sound hm ht
  refine ⟨nr, c, hny, hfar, hl, hm, ⟨r, hr⟩, fun r hr => ?_⟩
  have hsafe : SafeRook sk nr wk := Or.inl (by
    simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, hs, hbar⟩ := krk_safe_rank_reply hm.1 hm.2 hsafe
    (by change sk.2.val < nr.2.val; exact hb) hwy hr
  refine ⟨t, hmt, ⟨hb, hbar, ?_⟩⟩
  cases hs with
  | lone hd _ _ _ => simp only [dInf, absDiff] at *; omega

end EndgameChess.Rules
