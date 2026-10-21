import EndgameChess.Rules.KRKCentral.Definitions

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 2000000

/-- The hf2 king action required by initial centralisation/restoration. It
preserves the wall and all weak replies, but deliberately does NOT assert a
distant rook after the reply. This is the exact C052 Section3/8 dependency. -/
theorem king_below_pair {q : Position} {σ : Colour} {sk rs wk su : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hmove : dInf sk su=1) (hs : su.2.val<rs.2.val)
    (hw : rs.2.val<wk.2.val) (hf : 2≤absDiff rs.1.val wk.1.val) :
    ∃ c, Legal q c ∧ Matches c σ ⟨su,rs,wk,false⟩ ∧ (∃ v, Legal c v) ∧
      ∀ v, Legal c v → ∃ t, Matches v σ ⟨su,rs,t,true⟩ ∧
        rs.2.val<t.2.val ∧ absDiff t.1.val wk.1.val≤1 := by
  have hstep : StepM ⟨sk,rs,wk,true⟩ ⟨su,rs,wk,false⟩ := by
    refine StepM.king hmove ?_ ?_
    · simp only [ne_iff_coords]; omega
    · simp only [dInf,absDiff]; omega
  obtain ⟨c,hl,hm⟩ := step_sound hq hstep
  obtain ⟨t,ht⟩ := barrier_horizontal_reply_exists (sk := su) (rs := rs) (wk := wk)
    (by omega) hw hf
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  refine ⟨c,hl,hm,⟨v,hv⟩,?_⟩
  intro v hv
  have hsafe : SafeRook su rs wk := Or.inl (by simp only [dInf,absDiff] at *; omega)
  obtain ⟨t,hmt,hst,hyt⟩ := krk_safe_rank_reply (sk := su) (rs := rs) (wk := wk)
    hm.1 hm.2 hsafe hs hw hv
  refine ⟨t,hmt,hyt,?_⟩
  cases hst with
  | lone hd _ _ _ => simp only [dInf,absDiff] at *; omega

end EndgameChess.Rules.KRKCentral
