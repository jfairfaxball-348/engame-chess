import EndgameChess.Rules.KRKForcing.RookRescue

/-! EC-C015: rank contraction with at most one additional rook-rescue move. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

/-- Raise the barrier, then if a reply leaves the rook hanging, rescue it on the
strong turn. All defending reply sets are nonempty and all replies are covered. -/
theorem krk_rank_advance_rescue {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val + 2 ≤ wk.2.val)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) :
    ∃ nr c, nr.1.val = rs.1.val ∧ nr.2.val = rs.2.val + 1 ∧ Legal q c ∧
      Matches c σ ⟨sk, nr, wk, false⟩ ∧ (∃ r, Legal c r) ∧
      7 - nr.2.val < 7 - rs.2.val ∧
      ∀ r, Legal c r → ∃ t, Matches r σ ⟨sk, nr, t, true⟩ ∧
        (DistantBarrier sk nr t ∨
          ∃ sr d, sr.2 = nr.2 ∧ 4 ≤ absDiff sr.1.val t.1.val ∧ Legal r d ∧
            Matches d σ ⟨sk, sr, t, false⟩ ∧ (∃ v, Legal d v) ∧
            ∀ v, Legal d v → ∃ w, Matches v σ ⟨sk, sr, w, true⟩ ∧
              DistantBarrier sk sr w) := by
  let nr : Square := (rs.1, ⟨rs.2.val + 1, by omega⟩)
  have hx : nr.1.val = rs.1.val := rfl
  have hy : nr.2.val = rs.2.val + 1 := rfl
  obtain ⟨c, hl, hm⟩ := step_sound (σ := σ) (a := ⟨sk, rs, wk, true⟩)
    ⟨hk, ht⟩ (rank_advance_step hb hw hx hy)
  have hgap : sk.2.val + 2 ≤ wk.2.val := by omega
  have habove : nr.2.val < wk.2.val := by omega
  have hfile : 2 ≤ absDiff nr.1.val wk.1.val := by rw [hx]; exact hf
  obtain ⟨t, hstep⟩ := barrier_horizontal_reply_exists hgap habove hfile
  obtain ⟨r, hr, _⟩ := step_sound hm hstep
  refine ⟨nr, c, hx, hy, hl, hm, ⟨r, hr⟩, by omega, fun r hr => ?_⟩
  have hbelow : sk.2.val < nr.2.val := by omega
  have hsafe : SafeRook sk nr wk := Or.inl (by
    simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, _, htbar⟩ := krk_safe_rank_reply hm.1 hm.2 hsafe
    hbelow habove hr
  refine ⟨t, hmt, ?_⟩
  by_cases hs : 2 ≤ dInf nr t
  · exact Or.inl ⟨hbelow, htbar, hs⟩
  · exact Or.inr (krk_barrier_rook_rescue hmt hbelow htbar (by omega))

/-- Every proved upper-band phase image has the two-file margin needed by the
bounded rank-advance/rescue policy; no stronger margin is assumed. -/
theorem phase_image_file_margin {sk rs wk : Square} (hi : PhaseImage sk rs wk) :
    sk.2.val < rs.2.val ∧ 2 ≤ absDiff rs.1.val wk.1.val := by
  simp only [PhaseImage, absDiff] at *
  omega

/-- The bounded policy applies to every upper-band image, for arbitrary flags. -/
theorem krk_phase_image_upper_advance {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (hi : PhaseImage sk rs wk) (hupper : wk.2.val = rs.2.val + 2) :
    ∃ nr c, nr.1.val = rs.1.val ∧ nr.2.val = rs.2.val + 1 ∧ Legal q c ∧
      Matches c σ ⟨sk, nr, wk, false⟩ ∧ (∃ r, Legal c r) ∧
      7 - nr.2.val < 7 - rs.2.val ∧
      ∀ r, Legal c r → ∃ t, Matches r σ ⟨sk, nr, t, true⟩ ∧
        (DistantBarrier sk nr t ∨
          ∃ sr d, sr.2 = nr.2 ∧ 4 ≤ absDiff sr.1.val t.1.val ∧ Legal r d ∧
            Matches d σ ⟨sk, sr, t, false⟩ ∧ (∃ v, Legal d v) ∧
            ∀ v, Legal d v → ∃ w, Matches v σ ⟨sk, sr, w, true⟩ ∧
              DistantBarrier sk sr w) := by
  obtain ⟨hb, hf⟩ := phase_image_file_margin hi
  exact krk_rank_advance_rescue hk ht hb (by omega) hf

end EndgameChess.Rules
