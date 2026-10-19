import EndgameChess.Rules.KRKForcing.WallForce

/-! S029: a direct safe vertical setup subfamily; arbitrary setup remains open. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

/-- A distant rook on a file distinct from the strong king can enter a rank
wall directly. This is a setup subfamily, not all arbitrary KRK arrivals. -/
theorem krk_vertical_wall_entry_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hgap : sk.2.val + 2 ≤ wk.2.val)
    (hx : rs.1.val ≠ sk.1.val) (hf : 2 ≤ absDiff rs.1.val wk.1.val) :
    ForceMate σ q := by
  let nr : Square := (rs.1, ⟨sk.2.val + 1, by omega⟩)
  have hny : nr.2.val = sk.2.val + 1 := rfl
  by_cases hy : rs.2.val = sk.2.val + 1
  · exact krk_rank_wall_force hq (by omega) (by omega)
  have hs : StepM ⟨sk, rs, wk, true⟩ ⟨sk, nr, wk, false⟩ := by
    have hline : RookLine rs nr := ⟨fun h => hy h.2, Or.inl rfl⟩
    refine StepM.rook hline ?_ ?_ ?_ ?_ ?_ <;>
      (try dsimp only [nr] at *) <;> simp only [RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hs
  have hbelow : sk.2.val < nr.2.val := by omega
  have habove : nr.2.val < wk.2.val := by omega
  have hfile : 2 ≤ absDiff nr.1.val wk.1.val := hf
  obtain ⟨t, ht⟩ := barrier_horizontal_reply_exists (sk := sk) (rs := nr) (wk := wk)
    hgap habove hfile
  obtain ⟨r, hr, _⟩ := step_sound hm ht
  apply forceMate_choose hq.2 hl
  apply forceMate_defend hm.2 ⟨r, hr⟩
  intro r hr
  have hsafe : SafeRook sk nr wk := Or.inl (by simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, _, hbar⟩ := krk_safe_rank_reply (sk := sk) (rs := nr) (wk := wk)
    hm.1 hm.2 hsafe hbelow habove hr
  exact krk_rank_wall_force hmt hbelow hbar

end EndgameChess.Rules
