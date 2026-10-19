import EndgameChess.Rules.KRKForcing.OffRankSetup

/-! S030 / EC-C021: safe same-rank setup, including the back rank. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

private theorem weak_wall_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hm : Matches q σ ⟨sk, rs, wk, false⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val)
    (hs : SafeRook sk rs wk) (hne : ∃ r, Legal q r) : ForceMate σ q := by
  apply forceMate_defend hm.2 hne
  intro r hr
  obtain ⟨t, ht, _, hbar⟩ := krk_safe_rank_reply hm.1 hm.2 hs hb hw hr
  exact krk_rank_wall_force ht hb hbar

private theorem same_rank_no_file {sk rs wk : Square}
    (hneq : sk ≠ rs) (hrow : rs.2.val = sk.2.val)
    (hg : sk.2.val + 2 ≤ wk.2.val) (hn : ¬ RookSees rs wk sk wk) :
    rs.1.val ≠ wk.1.val := by
  intro e
  apply hn
  refine ⟨⟨?_, Or.inl e⟩, ?_, not_onSeg_end _ _⟩
  · omega
  · have hh := ne_iff_coords.1 hneq
    simp only [OnSeg] at *; omega

private theorem rank_zero_reply {sk rs wk : Square}
    (hs : sk.2.val = 0) (hr : rs.2.val ≤ 1) (hw : 2 ≤ wk.2.val)
    (hx : rs.1.val ≠ wk.1.val) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := by
  let y : Fin 8 := if h : wk.2.val = 2 then ⟨3, by decide⟩
    else ⟨wk.2.val - 1, by omega⟩
  have hy : 2 ≤ y.val ∧ absDiff wk.2.val y.val = 1 := by
    dsimp [y]; split <;> simp only [absDiff] <;> omega
  let t : Square := (wk.1, y)
  refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩
  all_goals (try dsimp only [t] at *)
  · simp only [dInf, absDiff] at *; omega
  · simp only [ne_iff_coords] at *; omega
  · simp only [dInf, absDiff] at *; omega
  · intro h
    have := h.1
    simp only [RookLine] at *; omega

/-- Same-rank strong king and rook can make a wall by a backwards king step. -/
theorem krk_same_rank_retreat_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hg : sk.2.val + 2 ≤ wk.2.val) (hy : rs.2.val = sk.2.val)
    (hpos : 0 < sk.2.val) (hn : ¬ RookSees rs wk sk wk) : ForceMate σ q := by
  have hx := same_rank_no_file (sk := sk) (rs := rs) (wk := wk) hq.1.1 hy hg hn
  let su : Square := (sk.1, ⟨sk.2.val - 1, by omega⟩)
  have hsy : su.2.val + 1 = sk.2.val := by dsimp [su]; omega
  have hs : StepM ⟨sk, rs, wk, true⟩ ⟨su, rs, wk, false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;> dsimp only [su] <;>
      simp only [dInf, absDiff, ne_iff_coords] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hs
  let t : Square := (wk.1, ⟨wk.2.val - 1, by omega⟩)
  have hrep : StepM ⟨su, rs, wk, false⟩ ⟨su, rs, t, true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      (try dsimp only [su, t] at *) <;>
      simp only [dInf, absDiff, ne_iff_coords, RookSees, RookLine, OnSeg] at * <;> omega
  obtain ⟨r, hr, _⟩ := step_sound hm hrep
  apply forceMate_choose hq.2 hl
  apply weak_wall_force hm (by omega) (by omega) ?_ ⟨r, hr⟩
  exact Or.inl (by simp only [dInf, absDiff] at *; omega)

/-- Protected rook entry on the back rank, with an explicit legal reply. -/
theorem krk_backrank_protected_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hs : sk.2.val = 0) (hr : rs.2.val = 0) (hw : 2 ≤ wk.2.val)
    (ha : absDiff sk.1.val rs.1.val = 1) (hn : ¬ RookSees rs wk sk wk) :
    ForceMate σ q := by
  have hx := same_rank_no_file (sk := sk) (rs := rs) (wk := wk) hq.1.1 (by omega) (by omega) hn
  let nr : Square := (rs.1, 1)
  have hnx : nr.1.val = rs.1.val := rfl
  have hny : nr.2.val = 1 := rfl
  have hstep : StepM ⟨sk, rs, wk, true⟩ ⟨sk, nr, wk, false⟩ := by
    have hline : RookLine rs nr := ⟨fun h => by have := h.2; omega, Or.inl rfl⟩
    refine StepM.rook hline ?_ ?_ ?_ ?_ ?_ <;>
      (try dsimp only [nr] at *) <;>
      simp only [RookLine, OnSeg, dInf, absDiff, ne_iff_coords] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hstep
  obtain ⟨t, ht⟩ := rank_zero_reply (sk := sk) (rs := nr) (wk := wk) hs (by omega) hw hx
  obtain ⟨r, hrep, _⟩ := step_sound hm ht
  apply forceMate_choose hq.2 hl
  apply weak_wall_force hm (by omega) (by omega) ?_ ⟨r, hrep⟩
  exact Or.inr (by simp only [dInf, absDiff] at *; omega)

/-- The remaining close-file back-rank case prepares the protected entry. -/
theorem krk_backrank_setup_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hs : sk.2.val = 0) (hr : rs.2.val = 0) (hw : 2 ≤ wk.2.val)
    (hclose : absDiff sk.1.val wk.1.val ≤ 1)
    (hf : absDiff rs.1.val wk.1.val ≤ 1) (hn : ¬ RookSees rs wk sk wk) :
    ForceMate σ q := by
  have hx := same_rank_no_file (sk := sk) (rs := rs) (wk := wk) hq.1.1 (by omega) (by omega) hn
  by_cases ha : absDiff sk.1.val rs.1.val = 1
  · exact krk_backrank_protected_force hq hs hr hw ha hn
  have hneq := ne_iff_coords.1 hq.1.1
  let su : Square := (wk.1, sk.2)
  have hsy : su.2.val = 0 := hs
  have hadj : absDiff su.1.val rs.1.val = 1 := by
    dsimp only [su]; simp only [absDiff] at *; omega
  have hstep : StepM ⟨sk, rs, wk, true⟩ ⟨su, rs, wk, false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;> dsimp only [su] <;>
      simp only [dInf, absDiff, ne_iff_coords] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hstep
  obtain ⟨t, ht⟩ := rank_zero_reply (sk := su) (rs := rs) (wk := wk) hsy (by omega) hw hx
  obtain ⟨r, hrep, _⟩ := step_sound hm ht
  apply forceMate_choose hq.2 hl
  apply forceMate_defend hm.2 ⟨r, hrep⟩
  intro r hrep
  have hsafe : SafeRook su rs wk := Or.inl (by simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, hst⟩ := krk_safe_reply (sk := su) (rs := rs) (wk := wk) hm.1 hm.2 hsafe hrep
  have hd : dInf wk t = 1 := by cases hst; assumption
  have hsep : 2 ≤ dInf su t := by cases hst; assumption
  have hty : 2 ≤ t.2.val := by
    dsimp only [su] at hsep
    simp only [dInf, absDiff] at *; omega
  have hgeom := krk_strong_arrival_geometry hrep hmt.1 hmt.2
  exact krk_backrank_protected_force hmt hsy hr hty hadj hgeom.2

end EndgameChess.Rules
