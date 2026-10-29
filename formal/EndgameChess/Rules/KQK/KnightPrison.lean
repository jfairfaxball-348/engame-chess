import EndgameChess.Rules.KQK.BandGeometry

/-! The top-right knight prison, with an arbitrary king below rank five.
This is the repair needed before advancing a separating rank near a corner. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def KnightBox (qs wk : Square) : Prop :=
  qs.1.val = 5 ∧ qs.2.val = 5 ∧ 5 < wk.1.val ∧ 5 < wk.2.val

def KnightPrison (qs wk : Square) : Prop :=
  qs.1.val = 5 ∧ qs.2.val = 5 ∧
    ((wk.1.val = 6 ∧ wk.2.val = 7) ∨ (wk.1.val = 7 ∧ wk.2.val = 6))

private theorem knight_prison_box {qs wk : Square} (hp : KnightPrison qs wk) :
    KnightBox qs wk := by
  obtain ⟨qx,qy,points⟩ := hp
  rcases points with ⟨wx,wy⟩ | ⟨wx,wy⟩ <;> exact ⟨qx,qy,by omega,by omega⟩

private theorem knight_prison_safe {sk qs wk : Square} (hp : KnightPrison qs wk) :
    SafeQueen sk qs wk := by
  obtain ⟨qx,qy,points⟩ := hp
  left
  rcases points with ⟨wx,wy⟩ | ⟨wx,wy⟩ <;> simp only [dInf,absDiff] <;> omega

private theorem knight_box_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (low : sk.2.val ≤ 4) (box : KnightBox qs wk) (safe : SafeQueen sk qs wk)
    (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ KnightPrison qs t ∧ dInf wk t = 1 := by
  obtain ⟨qx,qy,wx,wy⟩ := box
  obtain ⟨t,hm,hrt,wall,hd,hn,_⟩ := wall_reply hq ht ⟨by omega,by omega,by omega⟩ safe hl
  obtain ⟨_,ty,tx⟩ := wall
  have bx := t.1.isLt
  have by' := t.2.isLt
  have notNear : ¬ dInf qs t = 1 := fun h => hn (near_sees h)
  have notCorner : ¬ (t.1.val = 7 ∧ t.2.val = 7) := by
    rintro ⟨sevenX,sevenY⟩
    apply hn
    apply sees_split.mpr
    right
    refine ⟨?_,?_,?_⟩
    · simp only [KBK.onDiag,ne_iff_coords,absDiff]; omega
    · simp only [KBK.between,KBK.onDiag,dInf,absDiff,ne_iff_coords]; omega
    · simp [KBK.between,KBK.onDiag]
  have points : (t.1.val = 6 ∧ t.2.val = 7) ∨ (t.1.val = 7 ∧ t.2.val = 6) := by
    simp only [dInf,absDiff] at notNear
    omega
  exact ⟨t,hm,hrt,⟨qx,qy,points⟩,hd⟩

private theorem knight_box_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (low : sk.2.val ≤ 4) (box : KnightBox qs wk) : ∃ r, Legal q r := by
  obtain ⟨qx,qy,wx,wy⟩ := box
  exact wall_reply_exists hq ht ⟨by omega,by omega,by omega⟩ (Or.inr ⟨qy,by omega⟩)

private theorem knight_top_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 4) (qx : qs.1.val = 5) (qy : qs.2.val = 5)
    (wx : wk.1.val = 6) (wy : wk.2.val = 7) : MateWithin σ 27 q := by
  let nq : Square := (4,6)
  obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht
    (near_sees (by simp only [dInf,absDiff,nq]; omega))
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have edge : EdgeWall sk nq wk := ⟨by omega,rfl,wy,by decide,by dsimp [nq]; omega⟩
  exact mateWithin_choose ht hl (edge_wall_weak_bound hm hc edge)

/-- The queen knight prison can be widened without approaching the corner
with the king. A king tempo chooses the favourable parity of its two replies. -/
theorem knight_prison_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 4) (hp : KnightPrison qs wk) : MateWithin σ 29 q := by
  obtain ⟨qx,qy,points⟩ := hp
  rcases points with top | side
  · exact mateWithin_mono (knight_top_bound hq ht low qx qy top.1 top.2) (by decide)
  · let x : Fin 8 := ⟨if sk.1.val = 7 then 6 else sk.1.val+1,by
      have bound := sk.1.isLt; split <;> omega⟩
    let su : Square := (x,sk.2)
    have step : dInf sk su = 1 := by
      have bound := sk.1.isLt
      dsimp [dInf,absDiff,su,x]; split <;> omega
    obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht step
      (by simp only [ne_iff_coords,su]; omega)
      (by simp only [dInf,absDiff,su]; have := side.2; omega)
    have newLow : su.2.val ≤ 4 := low
    have box : KnightBox qs wk := knight_prison_box ⟨qx,qy,Or.inr side⟩
    apply mateWithin_pair ht hl hc (knight_box_reply_exists hm hc newLow box)
    intro r hr
    obtain ⟨t,hmt,hrt,htp,hd⟩ := knight_box_reply hm hc newLow box
      (knight_prison_safe ⟨qx,qy,Or.inr side⟩) hr
    have top : t.1.val = 6 ∧ t.2.val = 7 := by
      obtain ⟨_,_,cases⟩ := htp
      rcases cases with top | other
      · exact top
      · simp only [dInf,absDiff] at hd
        obtain ⟨wx,wy⟩ := side
        obtain ⟨tx,ty⟩ := other
        omega
    exact knight_top_bound hmt hrt newLow qx qy top.1 top.2

/-- One downward king step extends the prison finish to a king on rank five. -/
theorem knight_prison_low_five_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 5) (hp : KnightPrison qs wk) : MateWithin σ 31 q := by
  by_cases lower : sk.2.val ≤ 4
  · exact mateWithin_mono (knight_prison_bound hq ht lower hp) (by decide)
  have ky : sk.2.val = 5 := by omega
  have qy := hp.2.1
  have wy : 6 ≤ wk.2.val := by rcases hp.2.2 with top | side <;> omega
  let su : Square := (sk.1,4)
  obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; omega)
    (by simp only [dInf,absDiff,su]; omega)
  have box := knight_prison_box hp
  have newLow : su.2.val ≤ 4 := by change (4 : Nat) ≤ 4; decide
  apply mateWithin_pair ht hl hct (knight_box_reply_exists hm hct newLow box)
  intro r hr
  obtain ⟨t,hmt,hrt,next,_⟩ := knight_box_reply hm hct newLow box (knight_prison_safe hp) hr
  exact knight_prison_bound hmt hrt newLow next

/-- The checked corner and the two nonchecking knight squares share the
same safe weak-turn funnel. Safety excludes an unprotected queen capture. -/
theorem knight_box_weak_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (low : sk.2.val ≤ 4) (box : KnightBox qs wk) (safe : SafeQueen sk qs wk) :
    MateWithin σ 30 q := by
  apply mateWithin_defend ht (knight_box_reply_exists hq ht low box)
  intro r hr
  obtain ⟨t,hm,hrt,hp,_⟩ := knight_box_reply hq ht low box safe hr
  exact knight_prison_bound hm hrt low hp

/-- Repair the one-cell corner trap before making a king move. -/
theorem corner_knight_rescue {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 4) (qx : qs.1.val = 6) (qy : qs.2.val = 5)
    (wx : wk.1.val = 7) (wy : wk.2.val = 7) : MateWithin σ 31 q := by
  let nq : Square := (5,5)
  obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht
    (near_sees (by simp only [dInf,absDiff,nq]; omega))
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  exact mateWithin_choose ht hl (knight_box_weak_bound hm hc low
    ⟨rfl,rfl,by omega,by omega⟩ (Or.inl (by simp only [dInf,absDiff,nq]; omega)))

end EndgameChess.Rules.KQK
