import EndgameChess.Rules.KRKBox.Region

namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

private theorem box_pair {σ : Colour} {Q : Position → Prop} {n : Nat}
    {q : Position} {sk rs wk su nr : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hs : StepM ⟨sk,rs,wk,true⟩ ⟨su,nr,wk,false⟩)
    (hy : su.2.val+1 = nr.2.val) (hw : nr.2.val < wk.2.val)
    (hp : dInf su nr = 1)
    (hne : ∃ t, StepM ⟨su,nr,wk,false⟩ ⟨su,nr,t,true⟩)
    (hall : ∀ v t, Matches v σ ⟨su,nr,t,true⟩ → nr.2.val < t.2.val →
      absDiff t.1.val wk.1.val ≤ 1 → t.1.val ≠ nr.1.val →
      KRKBoxPhase σ Q n v) : KRKBoxPhase σ Q (n+1) q := by
  obtain ⟨c,hl,hm⟩ := step_sound hq hs
  obtain ⟨t,ht⟩ := hne
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  refine KRKBoxPhase.pair hq.2 hl hm.2 ⟨v,hv⟩ ?_
  intro v hv
  obtain ⟨t,hmt,hyt,hdt,hxt⟩ := krk_box_reply_region hm hy hw hp hv
  exact hall v t hmt hyt hdt hxt

/-- Actual all-defence guarded large-box contraction, normalized NE input.
The right branch finishes in two pairs; the crossing branch pays two more
escort pairs. No global mating or RAW/history conclusion is asserted. -/
theorem krk_guarded_large_box_phase {q : Position} {σ : Colour} {sk rs wk : Square}
    {a b : Nat} (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (ha : 1 ≤ a) (ha2 : a ≤ 2) (_hb : 1 ≤ b) (_hb6 : b ≤ 6)
    (hsx : sk.1.val+1 = a) (hsy : sk.2.val+1 = b)
    (hrx : rs.1.val = a) (hry : rs.2.val = b)
    (hwx : a < wk.1.val) (hwy : b < wk.2.val) :
    KRKBoxPhase σ (BoxCorner σ a b) 4 q := by
  let s1 : Square := (⟨a, by omega⟩, sk.2)
  let s2 : Square := (⟨a+1, by omega⟩, sk.2)
  let s3 : Square := (⟨a+2, by omega⟩, sk.2)
  let nr : Square := (⟨a+1, by omega⟩, rs.2)
  have hs1 : StepM ⟨sk,rs,wk,true⟩ ⟨s1,rs,wk,false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;>
      simp only [s1,dInf,absDiff,ne_iff_coords] at * <;> omega
  apply box_pair hq hs1 (by dsimp [s1]; omega) (by omega)
    (by simp only [s1,dInf,absDiff]; omega)
    (krk_box_reply_exists (lo := a+1) (hi := 7)
      (by dsimp [s1]; omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (by omega) (by omega))
  intro v w1 h1 hy1 hd1 hx1
  have hw1 : a < w1.1.val := by
    simp only [absDiff] at hd1
    omega
  have hr1 : StepM ⟨s1,rs,w1,true⟩ ⟨s1,nr,w1,false⟩ := by
    refine StepM.rook ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [s1,nr,RookLine,OnSeg,dInf,absDiff,ne_iff_coords, and_true, or_true] at * <;> omega
  apply box_pair h1 hr1 (by dsimp [s1,nr]; omega) (by dsimp [nr]; omega)
    (by simp only [s1,nr,dInf,absDiff]; omega)
    (krk_box_reply_exists (lo := a+2) (hi := 7)
      (by dsimp [s1,nr]; omega) (by dsimp [nr]; omega) (by omega) (by omega)
      (Or.inl (by dsimp [nr]; omega)) (by omega) (by omega))
  intro v2 w2 h2 hy2 hd2 hx2
  have hw2 : w2.1.val = a ∨ a+1 < w2.1.val := by
    simp only [absDiff] at hd2
    dsimp [nr] at hx2
    omega
  rcases hw2 with hleft | hright
  · have hs2 : StepM ⟨s1,nr,w2,true⟩ ⟨s2,nr,w2,false⟩ := by
      refine StepM.king ?_ ?_ ?_ <;>
        simp only [s1,s2,nr,dInf,absDiff,ne_iff_coords] at * <;> omega
    apply box_pair h2 hs2 (by dsimp [s2,nr]; omega) hy2
      (by simp only [s2,nr,dInf,absDiff]; omega)
      (krk_box_reply_exists (lo := 0) (hi := a)
        (by dsimp [s2,nr]; omega) hy2 (by omega) (by omega)
        (Or.inr (by dsimp [nr]; omega)) (by omega) (by omega))
    intro v3 w3 h3 hy3 hd3 hx3
    have hw3 : w3.1.val < a+1 := by
      simp only [absDiff] at hd3
      dsimp [nr] at hx3
      omega
    have hs3 : StepM ⟨s2,nr,w3,true⟩ ⟨s3,nr,w3,false⟩ := by
      refine StepM.king ?_ ?_ ?_ <;>
        simp only [s2,s3,nr,dInf,absDiff,ne_iff_coords] at * <;> omega
    apply box_pair h3 hs3 (by dsimp [s3,nr]; omega) hy3
      (by simp only [s3,nr,dInf,absDiff]; omega)
      (krk_box_reply_exists (lo := 0) (hi := a)
        (by dsimp [s3,nr]; omega) hy3 (by omega) (by omega)
        (Or.inr (by dsimp [nr]; omega)) (by omega) (by omega))
    intro v4 w4 h4 hy4 hd4 hx4
    have hw4 : w4.1.val < a+1 := by
      simp only [absDiff] at hd4
      dsimp [nr] at hx4
      omega
    apply KRKBoxPhase.done
    refine ⟨s3,nr,w4,h4,rfl,hry,?_,?_,Or.inr ⟨rfl,hw4⟩⟩
    · dsimp [s3]; exact hsy
    · dsimp [nr] at hy4; omega
  · apply KRKBoxPhase.done
    refine ⟨s1,nr,w2,h2,rfl,hry,?_,?_,Or.inl ⟨rfl,hright⟩⟩
    · dsimp [s1]; exact hsy
    · dsimp [nr] at hy2; omega

end EndgameChess.Rules
