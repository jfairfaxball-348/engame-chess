import EndgameChess.Rules.KRKCentral.KingBelow

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 2000000

/-- Ready upper exit advances one rank at margin2. Every weak reply keeps
the rook and strict wall; post-margin may be1 and is left for the costed
restoration, rather than charged as an unproved distant-rook conclusion. -/
theorem rank_two_pair {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hs : sk.2.val<rs.2.val) (hw : rs.2.val+2≤wk.2.val)
    (hf : 2≤absDiff rs.1.val wk.1.val) :
    ∃ nr c, nr.1=rs.1 ∧ nr.2.val=rs.2.val+1 ∧ Legal q c ∧
      Matches c σ ⟨sk,nr,wk,false⟩ ∧ (∃ v, Legal c v) ∧
      ∀ v, Legal c v → ∃ t, Matches v σ ⟨sk,nr,t,true⟩ ∧
        nr.2.val<t.2.val ∧ absDiff t.1.val wk.1.val≤1 := by
  let nr : Square := (rs.1,⟨rs.2.val+1,by omega⟩)
  have hs2 : StepM ⟨sk,rs,wk,true⟩ ⟨sk,nr,wk,false⟩ :=
    rank_advance_step hs hw rfl rfl
  obtain ⟨c,hl,hm⟩ := step_sound hq hs2
  have hnry : nr.2.val=rs.2.val+1 := rfl
  obtain ⟨t,ht⟩ := barrier_horizontal_reply_exists (sk := sk) (rs := nr) (wk := wk)
    (by omega) (by omega) (by exact hf)
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  refine ⟨nr,c,rfl,rfl,hl,hm,⟨v,hv⟩,?_⟩
  intro v hv
  have hsafe : SafeRook sk nr wk := Or.inl (by
    change 2≤max (absDiff rs.1.val wk.1.val) (absDiff nr.2.val wk.2.val)
    omega)
  obtain ⟨t,hmt,hst,hyt⟩ := krk_safe_rank_reply (sk := sk) (rs := nr) (wk := wk)
    hm.1 hm.2 hsafe (by omega) (by omega) hv
  refine ⟨t,hmt,hyt,?_⟩
  cases hst with
  | lone hd _ _ _ => simp only [dInf,absDiff] at *; omega

end EndgameChess.Rules.KRKCentral
