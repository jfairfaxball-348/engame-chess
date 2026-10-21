import EndgameChess.Rules.KRKBox.Definitions

namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

/-- Explicit horizontal reply in a nontrivial file interval off the rook ray.
The source may be one file outside the interval, including a rook-check source. -/
theorem krk_box_reply_exists {sk rs wk : Square} {lo hi : Nat}
    (hs : sk.2.val + 1 = rs.2.val) (hw : rs.2.val < wk.2.val)
    (hb : lo < hi) (hh : hi ≤ 7)
    (hr : rs.1.val < lo ∨ hi < rs.1.val)
    (hlo : lo ≤ wk.1.val + 1) (hhi : wk.1.val ≤ hi + 1) :
    ∃ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := by
  let x := if wk.1.val < lo then lo else if hi < wk.1.val then hi
    else if wk.1.val = lo then lo+1 else wk.1.val-1
  have hx : lo ≤ x ∧ x ≤ hi ∧ absDiff wk.1.val x = 1 := by
    dsimp [x]; split <;> (try split) <;> (try split) <;>
      simp only [absDiff] <;> omega
  let t : Square := (⟨x, by omega⟩, wk.2)
  refine ⟨t, StepM.lone ?_ ?_ ?_ ?_⟩
  · change max (absDiff wk.1.val x) (absDiff wk.2.val wk.2.val) = 1
    rw [hx.2.2]
    simp [absDiff]
  · simp only [t, ne_iff_coords] at *; omega
  · simp only [t, dInf, absDiff] at *; omega
  · simp only [t, RookSees, RookLine, OnSeg] at *; omega

end EndgameChess.Rules
