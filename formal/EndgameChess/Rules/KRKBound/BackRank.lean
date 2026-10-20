import EndgameChess.Rules.KRKBound.SameRank
import EndgameChess.Rules.KRKBound.ProtectedEntry
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

/-- The remaining close-file back-rank case prepares the protected entry. -/
theorem krk_backrank_setup_bound {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hs : sk.2.val = 0) (hr : rs.2.val = 0) (hw : 2 ≤ wk.2.val)
    (hclose : absDiff sk.1.val wk.1.val ≤ 1)
    (hf : absDiff rs.1.val wk.1.val ≤ 1) (hn : ¬ RookSees rs wk sk wk) :
    MateWithin σ 508 q := by
  have hx := bound_same_rank_no_file (sk := sk) (rs := rs) (wk := wk) hq.1.1 (by omega) (by omega) hn
  by_cases ha : absDiff sk.1.val rs.1.val = 1
  · exact mateWithin_mono (krk_backrank_protected_bound hq hs hr hw ha hn) (by decide)
  have hneq := ne_iff_coords.1 hq.1.1
  let su : Square := (wk.1, sk.2)
  have hsy : su.2.val = 0 := hs
  have hadj : absDiff su.1.val rs.1.val = 1 := by
    dsimp only [su]; simp only [absDiff] at *; omega
  have hstep : StepM ⟨sk, rs, wk, true⟩ ⟨su, rs, wk, false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;> dsimp only [su] <;>
      simp only [dInf, absDiff, ne_iff_coords] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hstep
  obtain ⟨t, ht⟩ := bound_rank_zero_reply (sk := su) (rs := rs) (wk := wk) hsy (by omega) hw hx
  obtain ⟨r, hrep, _⟩ := step_sound hm ht
  apply mateWithin_choose hq.2 hl
  apply mateWithin_defend hm.2 ⟨r, hrep⟩
  intro r hrep
  have hsafe : SafeRook su rs wk := Or.inl (by simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, hst⟩ := krk_safe_reply (sk := su) (rs := rs) (wk := wk) hm.1 hm.2 hsafe hrep
  have hd : dInf wk t = 1 := by cases hst; assumption
  have hsep : 2 ≤ dInf su t := by cases hst; assumption
  have hty : 2 ≤ t.2.val := by
    dsimp only [su] at hsep
    simp only [dInf, absDiff] at *; omega
  have hgeom := krk_strong_arrival_geometry hrep hmt.1 hmt.2
  exact krk_backrank_protected_bound hmt hsy hr hty hadj hgeom.2
end EndgameChess.Rules
