import EndgameChess.Rules.KRKForcing.Safety
import EndgameChess.Rules.ForceMate

/-! EC-C013: an opposed-kings checking phase. Symbolic geometry, all legal replies.
Paper: proofs/EC-C013_KRK_CHECK_PROGRESS.md. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

def Opposed (sk wk : Square) : Prop :=
  sk.1.val = wk.1.val ∧ wk.2.val = sk.2.val + 2

def checkRook (rs wk : Square) : Square := (rs.1, wk.2)

macro "phase_geo" : tactic =>
  `(tactic| (simp only [Opposed, checkRook, DistantBarrier, SafeRook, RookSees,
    RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega))

theorem rank_sees_of_below {sk rs t : Square}
    (hs : sk.2.val < rs.2.val) (hy : t.2.val = rs.2.val) (hne : t ≠ rs) :
    RookSees rs t sk t := by
  refine ⟨⟨?_, Or.inr hy.symm⟩, ?_, not_onSeg_end _ _⟩
  · rw [← ne_iff_coords]; exact Ne.symm hne
  · simp only [OnSeg]; omega

theorem opposition_check_step {sk rs wk : Square} (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val) :
    StepM ⟨sk, rs, wk, true⟩ ⟨sk, checkRook rs wk, wk, false⟩ := by
  refine StepM.rook ⟨fun h => hy h.2, Or.inl rfl⟩ ?_ ?_ ?_ ?_ ?_ <;> phase_geo

theorem opposition_edge_mate {sk rs wk : Square} (ho : Opposed sk wk)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val = wk.2.val)
    (hedge : wk.2.val = 7) : MateM ⟨sk, rs, wk, false⟩ := by
  refine ⟨rfl, rank_sees_of_below (by phase_geo) hy.symm (by phase_geo), ?_⟩
  intro t hd
  by_cases hlow : t.2.val < wk.2.val
  · left; phase_geo
  · right
    have hty : t.2.val = rs.2.val := by phase_geo
    have hne : t ≠ rs := by phase_geo
    exact ⟨hne, rank_sees_of_below (by phase_geo) hty hne⟩

/-- Every safe reply to the opposition check rises exactly one rank. -/
theorem opposition_reply_up {sk rs wk t : Square} (ho : Opposed sk wk)
    (hy : rs.2.val = wk.2.val) (hs : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩) :
    t.2.val = wk.2.val + 1 ∧ absDiff t.1.val wk.1.val ≤ 1 := by
  cases hs with
  | lone hd hne hfar hn =>
    have hneq : t.2.val ≠ wk.2.val := by
      intro he
      exact hn (rank_sees_of_below (by phase_geo) (by omega) hne)
    phase_geo

theorem opposition_up_reply_exists {sk rs wk : Square} (ho : Opposed sk wk)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val = wk.2.val)
    (htop : wk.2.val < 7) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := by
  let t : Square := (wk.1, ⟨wk.2.val + 1, by omega⟩)
  refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩ <;> dsimp [t] <;> phase_geo

/-- The chosen checking move mates at the edge, otherwise every legal reply rises.
The rook's four-file entry margin leaves it at least three files from every reply. -/
theorem krk_opposition_check {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val) :
    ∃ c, Legal q c ∧ Matches c σ ⟨sk, checkRook rs wk, wk, false⟩ ∧
      (MateGoal σ c ∨ ((∃ r, Legal c r) ∧ ∀ r, Legal c r →
        ∃ t, Matches r σ ⟨sk, checkRook rs wk, t, true⟩ ∧
          t.2.val = wk.2.val + 1 ∧ absDiff t.1.val wk.1.val ≤ 1 ∧
          3 ≤ absDiff rs.1.val t.1.val)) := by
  obtain ⟨c, hl, hm⟩ := step_sound (σ := σ) (a := ⟨sk, rs, wk, true⟩)
    ⟨hk, ht⟩ (opposition_check_step ho hf hy)
  refine ⟨c, hl, hm, ?_⟩
  by_cases hedge : wk.2.val = 7
  · exact Or.inl ⟨hm.2, mate_sound hm (opposition_edge_mate ho (rs := checkRook rs wk) (by change 2 ≤ absDiff rs.1.val wk.1.val; omega) rfl hedge)⟩
  · right
    have htop : wk.2.val < 7 := by omega
    obtain ⟨t, hs⟩ := opposition_up_reply_exists ho (rs := checkRook rs wk) (by change 2 ≤ absDiff rs.1.val wk.1.val; omega) rfl htop
    obtain ⟨r, hr, _⟩ := step_sound hm hs
    refine ⟨⟨r, hr⟩, fun r hr => ?_⟩
    have hsafe : SafeRook sk (checkRook rs wk) wk := Or.inl (by phase_geo)
    obtain ⟨t, hmt, hstep⟩ := krk_safe_reply hm.1 hm.2 hsafe hr
    obtain ⟨hty, htx⟩ := opposition_reply_up ho (rs := checkRook rs wk) rfl hstep
    exact ⟨t, hmt, hty, htx, by phase_geo⟩

/-- A symbolic mate-in-one family, not just a concrete example. -/
theorem krk_opposition_edge_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val)
    (hedge : wk.2.val = 7) : ForceMate σ q := by
  obtain ⟨c, hl, hm⟩ := step_sound (σ := σ) (a := ⟨sk, rs, wk, true⟩)
    ⟨hk, ht⟩ (opposition_check_step ho hf hy)
  exact forceMate_choose ht hl
    (forceMate_of_goal ⟨hm.2, mate_sound hm (opposition_edge_mate ho (rs := checkRook rs wk) (by change 2 ≤ absDiff rs.1.val wk.1.val; omega) rfl hedge)⟩)

theorem follow_horizontal_reply {sk rs wk t su : Square} (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val = wk.2.val)
    (hty : t.2.val = wk.2.val + 1) (htx : absDiff t.1.val wk.1.val ≤ 1)
    (hsx : su.1.val = sk.1.val) (hsy : su.2.val = sk.2.val + 1) :
    ∃ v, StepM ⟨su, rs, t, false⟩ ⟨su, rs, v, true⟩ := by
  by_cases hx : t.1.val < 7
  · let v : Square := (⟨t.1.val + 1, by omega⟩, t.2)
    refine ⟨v, StepM.lone ?_ ?_ ?_ ?_⟩ <;> dsimp [v] <;> phase_geo
  · let v : Square := (⟨t.1.val - 1, by omega⟩, t.2)
    refine ⟨v, StepM.lone ?_ ?_ ?_ ?_⟩ <;> dsimp [v] <;> phase_geo

/-- The fixed king step after any first reply has legal replies, all with rank
progress and a still-distant rook. This is the second half of the four-ply phase. -/
theorem krk_follow_check {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hq : Matches q σ ⟨sk, rs, t, true⟩) (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val = wk.2.val)
    (hty : t.2.val = wk.2.val + 1) (htx : absDiff t.1.val wk.1.val ≤ 1) :
    ∃ su u, su.1.val = sk.1.val ∧ su.2.val = sk.2.val + 1 ∧ Legal q u ∧
      Matches u σ ⟨su, rs, t, false⟩ ∧ (∃ v, Legal u v) ∧
      ∀ v, Legal u v → ∃ w, Matches v σ ⟨su, rs, w, true⟩ ∧
        DistantBarrier su rs w ∧ 7 - w.2.val < 7 - wk.2.val := by
  let su : Square := (sk.1, ⟨sk.2.val + 1, by have := ho.2; omega⟩)
  have hsx : su.1.val = sk.1.val := rfl
  have hsy : su.2.val = sk.2.val + 1 := rfl
  have hs : StepM ⟨sk, rs, t, true⟩ ⟨su, rs, t, false⟩ := by
    have htg : t.2.val = sk.2.val + 3 := by have hh := ho.2; omega
    have hrg : rs.2.val = sk.2.val + 2 := by have hh := ho.2; omega
    clear hf htx hq
    refine StepM.king ?_ ?_ ?_
    · dsimp only [su]; simp only [dInf, absDiff]; omega
    · intro he
      have he' := congrArg (fun x : Square => x.2.val) he
      dsimp only [su] at he'
      omega
    · dsimp only [su]; simp only [dInf, absDiff]; omega
  obtain ⟨u, hu, hmu⟩ := step_sound hq hs
  obtain ⟨v, hv⟩ := follow_horizontal_reply ho hf hy hty htx hsx hsy
  obtain ⟨v, hlegv, _⟩ := step_sound hmu hv
  refine ⟨su, u, hsx, hsy, hu, hmu, ⟨v, hlegv⟩, fun v hv => ?_⟩
  have hsafe : SafeRook su rs t := Or.inl (by phase_geo)
  have hku : IsKRK u σ su rs t := hmu.1
  have htu : u.turn = σ.opp := hmu.2
  have hbelow : su.2.val < rs.2.val := by
    dsimp only [su]
    have hh := ho.2
    omega
  have habove : rs.2.val < t.2.val := by omega
  obtain ⟨w, hmw, hstep, hyw⟩ := krk_safe_rank_reply (sk := su) (rs := rs) (wk := t)
    hku htu hsafe hbelow habove hv
  refine ⟨w, hmw, ⟨hbelow, hyw, ?_⟩, by omega⟩
  cases hstep with
  | lone hd _ _ _ => phase_geo

/-- The explicit four-ply phase: check; every reply; king-up; every reply.
The resulting distant-rook barrier has strictly smaller upper-rank potential. -/
theorem krk_opposition_four_ply {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (ho : Opposed sk wk)
    (hf : 4 ≤ absDiff rs.1.val wk.1.val) (hy : rs.2.val ≠ wk.2.val) :
    ∃ c, Legal q c ∧ Matches c σ ⟨sk, checkRook rs wk, wk, false⟩ ∧
      (MateGoal σ c ∨ ((∃ r, Legal c r) ∧ ∀ r, Legal c r →
        ∃ t, Matches r σ ⟨sk, checkRook rs wk, t, true⟩ ∧
          ∃ su u, su.1.val = sk.1.val ∧ su.2.val = sk.2.val + 1 ∧ Legal r u ∧
            Matches u σ ⟨su, checkRook rs wk, t, false⟩ ∧ (∃ v, Legal u v) ∧
            ∀ v, Legal u v → ∃ w, Matches v σ ⟨su, checkRook rs wk, w, true⟩ ∧
              DistantBarrier su (checkRook rs wk) w ∧
              7 - w.2.val < 7 - wk.2.val)) := by
  obtain ⟨c, hl, hm, hg | ⟨hn, hall⟩⟩ := krk_opposition_check hk ht ho hf hy
  · exact ⟨c, hl, hm, Or.inl hg⟩
  · refine ⟨c, hl, hm, Or.inr ⟨hn, fun r hr => ?_⟩⟩
    obtain ⟨t, hmt, hty, htx, _⟩ := hall r hr
    exact ⟨t, hmt, krk_follow_check hmt ho (by exact hf) rfl hty htx⟩

end EndgameChess.Rules
