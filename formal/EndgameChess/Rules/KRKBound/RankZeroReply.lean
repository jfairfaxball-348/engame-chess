import EndgameChess.Rules.KRKBound.SameRankFile
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000
theorem bound_rank_zero_reply {sk rs wk : Square}
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
end EndgameChess.Rules
