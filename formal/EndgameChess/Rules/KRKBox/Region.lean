import EndgameChess.Rules.KRKBox.Reply

namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

/-- Every actual legal weak reply to a protected box stays above its horizontal
ray and off its vertical ray; captures and arbitrary weak flag branches included. -/
theorem krk_box_reply_region {q r : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,false⟩)
    (hs : sk.2.val+1 = rs.2.val) (hw : rs.2.val < wk.2.val)
    (hp : dInf sk rs = 1) (hl : Legal q r) :
    ∃ t, Matches r σ ⟨sk,rs,t,true⟩ ∧ rs.2.val < t.2.val ∧
      absDiff t.1.val wk.1.val ≤ 1 ∧ t.1.val ≠ rs.1.val := by
  obtain ⟨t,hm,hstep,hy⟩ := krk_safe_rank_reply (sk := sk) (rs := rs) (wk := wk)
    hq.1 hq.2 (Or.inr hp) (by omega) hw hl
  refine ⟨t,hm,hy,?_,?_⟩
  · cases hstep with
    | lone hd _ _ _ => simp only [dInf,absDiff] at *; omega
  · cases hstep with
    | lone hd hn hf hsee =>
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords] at *
      omega

end EndgameChess.Rules
