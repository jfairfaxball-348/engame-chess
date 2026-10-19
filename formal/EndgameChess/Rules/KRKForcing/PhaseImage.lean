import EndgameChess.Rules.KRKForcing.CheckProgress

/-! EC-C014: the actual two-reply image of the frozen checking phase. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

/-- Bounds proved for the fixed checking/king-up choices, not a closed strategy. -/
def PhaseImage (sk rs wk : Square) : Prop :=
  rs.2.val = sk.2.val + 1 ∧
  (wk.2.val = rs.2.val + 1 ∨ wk.2.val = rs.2.val + 2) ∧
  absDiff wk.1.val sk.1.val ≤ 2 ∧ 4 ≤ absDiff rs.1.val sk.1.val ∧
  2 ≤ dInf rs wk

theorem phase_image_of_replies {sk rs wk t su w : Square}
    (ho : Opposed sk wk) (hf : 4 ≤ absDiff rs.1.val wk.1.val)
    (hy : rs.2.val = wk.2.val) (hty : t.2.val = wk.2.val + 1)
    (htx : absDiff t.1.val wk.1.val ≤ 1)
    (hsx : su.1.val = sk.1.val) (hsy : su.2.val = sk.2.val + 1)
    (hstep : StepM ⟨su, rs, t, false⟩ ⟨su, rs, w, true⟩) :
    PhaseImage su rs w := by
  cases hstep with
  | lone hd hne hfar hn =>
    have hb : su.2.val < rs.2.val := by obtain ⟨_, hh⟩ := ho; omega
    have hw : rs.2.val < t.2.val := by omega
    have hbar := rook_rank_barrier hb hw hd hne hn
    simp only [PhaseImage, Opposed, dInf, absDiff] at *
    omega

theorem krk_follow_check_image {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hq : Matches q σ ⟨sk, rs, t, true⟩) (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val = wk.2.val)
    (hty : t.2.val = wk.2.val + 1) (htx : absDiff t.1.val wk.1.val ≤ 1) :
    ∃ su u, su.1.val = sk.1.val ∧ su.2.val = sk.2.val + 1 ∧ Legal q u ∧
      Matches u σ ⟨su, rs, t, false⟩ ∧ (∃ v, Legal u v) ∧
      ∀ v, Legal u v → ∃ w, Matches v σ ⟨su, rs, w, true⟩ ∧
        PhaseImage su rs w ∧ 7 - w.2.val < 7 - wk.2.val := by
  obtain ⟨su, u, hsx, hsy, hu, hmu, hne, hall⟩ :=
    krk_follow_check hq ho hf hy hty htx
  refine ⟨su, u, hsx, hsy, hu, hmu, hne, fun v hv => ?_⟩
  have hsafe : SafeRook su rs t := Or.inl (by
    simp only [Opposed, dInf, absDiff] at *; omega)
  obtain ⟨w, hmw, hs⟩ := krk_safe_reply hmu.1 hmu.2 hsafe hv
  have him := phase_image_of_replies ho hf hy hty htx hsx hsy hs
  refine ⟨w, hmw, him, ?_⟩
  have hh := him.2.1
  omega

/-- A chosen check, all first replies, chosen king-up, and all second replies,
with exact legal ancestry and the proved image bounds. -/
theorem krk_opposition_phase_image {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val) :
    ∃ c, Legal q c ∧ Matches c σ ⟨sk, checkRook rs wk, wk, false⟩ ∧
      (MateGoal σ c ∨ ((∃ r, Legal c r) ∧ ∀ r, Legal c r →
        ∃ t, Matches r σ ⟨sk, checkRook rs wk, t, true⟩ ∧
          ∃ su u, su.1.val = sk.1.val ∧ su.2.val = sk.2.val + 1 ∧ Legal r u ∧
            Matches u σ ⟨su, checkRook rs wk, t, false⟩ ∧ (∃ v, Legal u v) ∧
            ∀ v, Legal u v → ∃ w, Matches v σ ⟨su, checkRook rs wk, w, true⟩ ∧
              PhaseImage su (checkRook rs wk) w ∧
              7 - w.2.val < 7 - wk.2.val)) := by
  obtain ⟨c, hl, hm, hg | ⟨hne, hall⟩⟩ := krk_opposition_check hk ht ho hf hy
  · exact ⟨c, hl, hm, Or.inl hg⟩
  · refine ⟨c, hl, hm, Or.inr ⟨hne, fun r hr => ?_⟩⟩
    obtain ⟨t, hmt, hty, htx, _⟩ := hall r hr
    exact ⟨t, hmt, krk_follow_check_image hmt ho hf rfl hty htx⟩

end EndgameChess.Rules
