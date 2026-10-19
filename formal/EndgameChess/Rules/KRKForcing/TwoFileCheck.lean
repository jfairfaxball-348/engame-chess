import EndgameChess.Rules.KRKForcing.WallActions

/-! EC-C016: a two-file checking action, without the frozen four-ply follow-up. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

theorem opposition_check_step_two {sk rs wk : Square} (ho : Opposed sk wk)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val) :
    StepM ⟨sk, rs, wk, true⟩ ⟨sk, checkRook rs wk, wk, false⟩ := by
  refine StepM.rook ⟨fun h => hy h.2, Or.inl rfl⟩ ?_ ?_ ?_ ?_ ?_ <;> phase_geo

theorem krk_opposition_check_two {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩) (ho : Opposed sk wk)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val) :
    ∃ c, Legal q c ∧ Matches c σ ⟨sk, checkRook rs wk, wk, false⟩ ∧
      (MateGoal σ c ∨ ((∃ r, Legal c r) ∧ ∀ r, Legal c r →
        ∃ t, Matches r σ ⟨sk, checkRook rs wk, t, true⟩ ∧
          t.2.val = wk.2.val + 1 ∧ absDiff t.1.val wk.1.val ≤ 1)) := by
  obtain ⟨c, hl, hm⟩ := step_sound hq (opposition_check_step_two ho hf hy)
  refine ⟨c, hl, hm, ?_⟩
  by_cases hedge : wk.2.val = 7
  · exact Or.inl ⟨hm.2, mate_sound hm (opposition_edge_mate ho (rs := checkRook rs wk) hf rfl hedge)⟩
  · obtain ⟨t, hs⟩ := opposition_up_reply_exists ho (rs := checkRook rs wk) hf rfl (by omega)
    obtain ⟨r, hr, _⟩ := step_sound hm hs
    refine Or.inr ⟨⟨r, hr⟩, fun r hr => ?_⟩
    have hsafe : SafeRook sk (checkRook rs wk) wk := Or.inl (by phase_geo)
    obtain ⟨t, hmt, hs⟩ := krk_safe_reply (sk := sk) (rs := checkRook rs wk) (wk := wk) hm.1 hm.2 hsafe hr
    obtain ⟨hty, htx⟩ := opposition_reply_up ho (rs := checkRook rs wk) rfl hs
    exact ⟨t, hmt, hty, htx⟩

/-- Actual named-colour mate at the upper edge with only two files of margin. -/
theorem krk_two_file_edge_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩) (ho : Opposed sk wk)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val)
    (hedge : wk.2.val = 7) : ForceMate σ q := by
  obtain ⟨c, hl, hm⟩ := step_sound hq (opposition_check_step_two ho hf hy)
  exact forceMate_choose hq.2 hl (forceMate_of_goal
    ⟨hm.2, mate_sound hm (opposition_edge_mate ho (rs := checkRook rs wk) hf rfl hedge)⟩)

end EndgameChess.Rules
