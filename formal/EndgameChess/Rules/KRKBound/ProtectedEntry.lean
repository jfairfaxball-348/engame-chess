import EndgameChess.Rules.KRKBound.SetupGeometry
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

/-- Protected rook entry on the back rank, with an explicit legal reply. -/
theorem krk_backrank_protected_bound {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hs : sk.2.val = 0) (hr : rs.2.val = 0) (hw : 2 ≤ wk.2.val)
    (ha : absDiff sk.1.val rs.1.val = 1) (hn : ¬ RookSees rs wk sk wk) :
    MateWithin σ 506 q := by
  have hx := bound_same_rank_no_file (sk := sk) (rs := rs) (wk := wk) hq.1.1 (by omega) (by omega) hn
  let nr : Square := (rs.1, 1)
  have hnx : nr.1.val = rs.1.val := rfl
  have hny : nr.2.val = 1 := rfl
  have hstep : StepM ⟨sk, rs, wk, true⟩ ⟨sk, nr, wk, false⟩ := by
    have hline : RookLine rs nr := ⟨fun h => by have := h.2; omega, Or.inl rfl⟩
    refine StepM.rook hline ?_ ?_ ?_ ?_ ?_ <;>
      (try dsimp only [nr] at *) <;>
      simp only [RookLine, OnSeg, dInf, absDiff, ne_iff_coords] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hstep
  obtain ⟨t, ht⟩ := bound_rank_zero_reply (sk := sk) (rs := nr) (wk := wk) hs (by omega) hw hx
  obtain ⟨r, hrep, _⟩ := step_sound hm ht
  apply mateWithin_choose hq.2 hl
  apply bound_weak_wall hm (by omega) (by omega) ?_ ⟨r, hrep⟩
  exact Or.inr (by simp only [dInf, absDiff] at *; omega)
end EndgameChess.Rules
