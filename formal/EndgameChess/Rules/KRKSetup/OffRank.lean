import EndgameChess.Rules.KRKSetup.HorizontalEntry
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000

set_option maxHeartbeats 2000000

private theorem bound_offrank_reply_exists {sk rs wk : Square}
    (hg : sk.2.val + 2 ≤ wk.2.val) (hy : rs.2.val ≠ wk.2.val)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := by
  let x : Fin 8 := if h : wk.1.val < 7 then ⟨wk.1.val + 1, by omega⟩
    else ⟨wk.1.val - 1, by omega⟩
  have hd : absDiff wk.1.val x.val = 1 := by
    dsimp [x]; split <;> simp only [absDiff] <;> omega
  let t : Square := (x, wk.2)
  refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩
  all_goals (try dsimp only [t] at *)
  · simp only [dInf, absDiff] at *; omega
  · simp only [ne_iff_coords, absDiff] at *; omega
  · simp only [dInf, absDiff] at *; omega
  · intro h
    have := h.1
    simp only [RookLine, absDiff] at *; omega

private theorem setup_offrank_distant_budget {q : Position} {σ : Colour} {sk rs wk : Square}
    (hwall : KRKWallBudget σ B)
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hg : sk.2.val + 2 ≤ wk.2.val)
    (hy : rs.2.val < sk.2.val ∨ wk.2.val < rs.2.val)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) : MateWithin σ (B + 2) q := by
  by_cases hx : rs.1.val ≠ sk.1.val
  · exact setup_clear_entry_budget hwall hq hg (Or.inl hx) hf
  · by_cases hr : sk.2.val < rs.2.val
    · exact setup_clear_entry_budget hwall hq hg (Or.inr hr) hf
    · apply setup_horizontal_entry_budget hwall hq
      · simp only [absDiff] at *; omega
      · omega
      · simp only [absDiff] at *; omega

/-- Exact strong-turn KRK, positive rank gap, no incoming rook check, and
rook off the strong king's rank: safe setup reaches a winning oriented wall. -/
theorem setup_offrank_budget {q : Position} {σ : Colour} {sk rs wk : Square}
    (hwall : KRKWallBudget σ B)
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hg : sk.2.val + 2 ≤ wk.2.val)
    (hy : rs.2.val ≠ sk.2.val) (hn : ¬ RookSees rs wk sk wk) : MateWithin σ (B + 4) q := by
  have hwy : rs.2.val ≠ wk.2.val := by
    intro e
    apply hn
    refine ⟨⟨?_, Or.inr e⟩, ?_, not_onSeg_end _ _⟩
    · exact ne_iff_coords.1 hq.1.2.2.1
    · simp only [OnSeg] at *; omega
  by_cases hb : sk.2.val < rs.2.val ∧ rs.2.val < wk.2.val
  · exact mateWithin_mono (hwall hq hb.1 hb.2) (by omega)
  have hout : rs.2.val < sk.2.val ∨ wk.2.val < rs.2.val := by omega
  by_cases hf : 2 ≤ absDiff rs.1.val wk.1.val
  · exact mateWithin_mono (setup_offrank_distant_budget hwall hq hg hout hf) (by omega)
  let nr : Square := (wallFarFile wk.1, rs.2)
  have hfar : 4 ≤ absDiff nr.1.val wk.1.val := wall_far_margin wk.1
  have hny : nr.2.val = rs.2.val := rfl
  have hs : StepM ⟨sk, rs, wk, true⟩ ⟨sk, nr, wk, false⟩ := by
    have hline : RookLine rs nr := by
      refine ⟨?_, Or.inr rfl⟩
      intro he
      have hh : rs.1.val = nr.1.val := he.1
      rw [hh] at hf
      omega
    refine StepM.rook hline ?_ ?_ ?_ ?_ ?_ <;>
      (try dsimp only [nr] at *) <;>
      simp only [RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hs
  obtain ⟨t, ht⟩ := bound_offrank_reply_exists (sk := sk) (rs := nr) (wk := wk) hg hwy (by omega)
  obtain ⟨r, hr, _⟩ := step_sound hm ht
  apply mateWithin_pair hq.2 hl hm.2 ⟨r, hr⟩
  intro r hr
  have hsafe : SafeRook sk nr wk := Or.inl (by simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, hstep⟩ := krk_safe_reply (sk := sk) (rs := nr) (wk := wk) hm.1 hm.2 hsafe hr
  have hd : dInf wk t = 1 := by cases hstep; assumption
  have hsep : 2 ≤ dInf sk t := by cases hstep; assumption
  have hfile : 2 ≤ absDiff nr.1.val t.1.val := by
    simp only [dInf, absDiff] at *; omega
  by_cases hgap : sk.2.val + 2 ≤ t.2.val
  · by_cases hx : nr.1.val ≠ sk.1.val
    · exact setup_clear_entry_budget hwall hmt hgap (Or.inl hx) hfile
    · by_cases hup : sk.2.val < nr.2.val
      · exact setup_clear_entry_budget hwall hmt hgap (Or.inr hup) hfile
      · apply setup_horizontal_entry_budget hwall hmt
        · simp only [absDiff] at *; omega
        · dsimp only [nr]; omega
        · dsimp only [nr]; simp only [absDiff] at *; omega
  · apply setup_horizontal_entry_budget hwall hmt
    · simp only [dInf, absDiff] at *; omega
    · dsimp only [nr]; omega
    · dsimp only [nr]; simp only [dInf, absDiff] at *; omega
end EndgameChess.Rules
