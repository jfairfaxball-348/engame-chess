import EndgameChess.Rules.KRKForcing.PhaseImage

/-! EC-C015: a two-ply distant-rook barrier contraction, not a repeated policy. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

theorem rank_advance_step {sk rs wk nr : Square}
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val + 2 ≤ wk.2.val)
    (hx : nr.1.val = rs.1.val) (hy : nr.2.val = rs.2.val + 1) :
    StepM ⟨sk, rs, wk, true⟩ ⟨sk, nr, wk, false⟩ := by
  refine StepM.rook ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega

theorem rank_advance_reply_exists {sk rs wk : Square}
    (hb : sk.2.val + 2 ≤ rs.2.val) (hw : rs.2.val < wk.2.val)
    (hf : 3 ≤ absDiff rs.1.val wk.1.val) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := by
  by_cases hx : wk.1.val < 7
  · let t : Square := (⟨wk.1.val + 1, by omega⟩, wk.2)
    refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩ <;> dsimp [t] <;>
      simp only [RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega
  · let t : Square := (⟨wk.1.val - 1, by omega⟩, wk.2)
    refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩ <;> dsimp [t] <;>
      simp only [RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega

/-- Chosen legal rook-up move and every defending reply, with a nonempty reply
set, a still-distant barrier and a strictly raised confinement rank. -/
theorem krk_rank_advance {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val + 2 ≤ wk.2.val)
    (hf : 3 ≤ absDiff rs.1.val wk.1.val) :
    ∃ nr c, nr.1.val = rs.1.val ∧ nr.2.val = rs.2.val + 1 ∧ Legal q c ∧
      Matches c σ ⟨sk, nr, wk, false⟩ ∧ (∃ r, Legal c r) ∧
      7 - nr.2.val < 7 - rs.2.val ∧
      ∀ r, Legal c r → ∃ t, Matches r σ ⟨sk, nr, t, true⟩ ∧
        DistantBarrier sk nr t := by
  let nr : Square := (rs.1, ⟨rs.2.val + 1, by omega⟩)
  have hx : nr.1.val = rs.1.val := rfl
  have hy : nr.2.val = rs.2.val + 1 := rfl
  obtain ⟨c, hl, hm⟩ := step_sound (σ := σ) (a := ⟨sk, rs, wk, true⟩)
    ⟨hk, ht⟩ (rank_advance_step hb hw hx hy)
  have hbelow : sk.2.val + 2 ≤ nr.2.val := by omega
  have habove : nr.2.val < wk.2.val := by omega
  have hfile : 3 ≤ absDiff nr.1.val wk.1.val := by rw [hx]; exact hf
  obtain ⟨t, hstep⟩ := rank_advance_reply_exists hbelow habove hfile
  obtain ⟨r, hr, _⟩ := step_sound hm hstep
  refine ⟨nr, c, hx, hy, hl, hm, ⟨r, hr⟩, by omega, fun r hr => ?_⟩
  have hsafe : SafeRook sk nr wk := Or.inl (by
    simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, hs, htbar⟩ := krk_safe_rank_reply hm.1 hm.2 hsafe
    (by change sk.2.val < nr.2.val; omega) habove hr
  refine ⟨t, hmt, ⟨by omega, htbar, ?_⟩⟩
  cases hs with
  | lone hd _ _ _ => simp only [dInf, absDiff] at *; omega

end EndgameChess.Rules
