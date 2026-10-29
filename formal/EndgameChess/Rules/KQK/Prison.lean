import EndgameChess.Rules.KQK.EdgeForce

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def Prison (qs wk : Square) : Prop :=
  qs.1.val = 4 ∧ qs.2.val = 6 ∧ wk.2.val = 7 ∧ 6 ≤ wk.1.val

def OutsidePrison (sk : Square) : Prop := sk.2.val ≤ 5 ∨ sk.1.val ≤ 4

theorem prison_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hp : Prison qs wk) (hs : OutsidePrison sk) : ∃ r, Legal q r := by
  obtain ⟨hqx,hqy,hwy,hwx⟩ := hp
  let x : Fin 8 := ⟨if wk.1.val = 7 then 6 else 7,by split <;> omega⟩
  let t : Square := (x,7)
  have hx : 6 ≤ x.val ∧ absDiff wk.1.val x.val = 1 := by
    have bound := wk.1.isLt
    dsimp [x]; split <;> simp only [absDiff] <;> omega
  have step : dInf wk t = 1 := by simp only [dInf,absDiff,t] at hx ⊢; omega
  have ne : t ≠ qs := by simp only [ne_iff_coords,t]; omega
  have far : 2 ≤ dInf sk t := by
    rcases hs with hs | hs <;> simp only [dInf,absDiff,t] <;> omega
  have notSeen : ¬ QueenSees qs t sk t := by
    apply not_sees_of_not_line
    · dsimp [t]; omega
    · dsimp [t]; omega
    · simp only [absDiff,t]; omega
  obtain ⟨r,hr,_,_⟩ := weak_move hq ht step ne far notSeen
  exact ⟨r,hr⟩

theorem prison_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hp : Prison qs wk) (hs : OutsidePrison sk) (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ Prison qs t := by
  obtain ⟨hqx,hqy,hwy,hwx⟩ := hp
  have safe : SafeQueen sk qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
  obtain ⟨t,hm,hr,hd,_,hn⟩ := safe_reply hq ht safe hl
  have bounds : 5 ≤ t.1.val ∧ 6 ≤ t.2.val := by
    simp only [dInf,absDiff] at hd; omega
  have ty : t.2.val = 7 := by
    have bound := t.2.isLt
    by_cases hy : t.2.val = 7
    · exact hy
    · have y6 : t.2.val = 6 := by omega
      apply False.elim
      apply hn
      apply rook_sees_queen
      refine ⟨⟨by omega,Or.inr (by omega)⟩,?_,not_onSeg_end _ _⟩
      · rcases hs with hs | hs <;> simp only [OnSeg] <;> omega
  have tx : 6 ≤ t.1.val := by
    by_cases hx : 6 ≤ t.1.val
    · exact hx
    · exact False.elim (hn (near_sees (by simp only [dInf,absDiff]; omega)))
  exact ⟨t,hm,hr,hqx,hqy,ty,tx⟩

private theorem rank_six_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prison qs wk) (hy : sk.2.val = 6) : MateWithin σ 17 q := by
  let su : Square := (sk.1,5)
  obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; have := hp.2.1; omega)
    (by simp only [dInf,absDiff,su]; have := hp.2.2.1; omega)
  have wall : EdgeWall su qs wk := ⟨by dsimp [su]; omega,hp.2.1,hp.2.2.1,
    by have := hp.1; omega,by have := hp.1; have := hp.2.2.2; omega⟩
  have replies := edge_reply_exists hm hc wall
  apply mateWithin_pair ht hl hc replies
  intro r hr
  obtain ⟨t,hmt,hrt,het,_⟩ := edge_reply hm hc wall hr
  exact corner_prison_fifteen hmt hrt ⟨het,hp.1⟩

private theorem top_left_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prison qs wk) (hy : sk.2.val = 7) (hx : sk.1.val ≤ 4) :
    MateWithin σ 19 q := by
  let x : Fin 8 := ⟨if sk.1.val = 4 then 3 else sk.1.val,by split <;> omega⟩
  let su : Square := (x,6)
  have sx : x.val ≤ 3 ∧ absDiff sk.1.val x.val ≤ 1 := by
    dsimp [x]; split <;> simp only [absDiff] <;> omega
  obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su] at sx ⊢; omega)
    (by simp only [ne_iff_coords,su]; have := hp.1; omega)
    (by simp only [dInf,absDiff,su]; have := hp.2.2.2; omega)
  have outside : OutsidePrison su := Or.inr (by dsimp [su]; omega)
  apply mateWithin_pair ht hl hc (prison_reply_exists hm hc hp outside)
  intro r hr
  obtain ⟨t,hmt,hrt,hpt⟩ := prison_reply hm hc hp outside hr
  exact rank_six_bound hmt hrt hpt rfl

/-- The two-square prison is winning even when the strong king starts above
the queen wall. Moving the king out first preserves an actual escape square. -/
theorem prison_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prison qs wk) (hfar : 2 ≤ dInf sk wk) : MateWithin σ 21 q := by
  by_cases low : sk.2.val ≤ 5
  · have wall : EdgeWall sk qs wk :=
      ⟨low,hp.2.1,hp.2.2.1,by have := hp.1; omega,
        by have := hp.1; have := hp.2.2.2; omega⟩
    exact mateWithin_mono (corner_prison_fifteen hq ht ⟨wall,hp.1⟩) (by decide)
  by_cases six : sk.2.val = 6
  · exact mateWithin_mono (rank_six_bound hq ht hp six) (by decide)
  have top : sk.2.val = 7 := by have bound := sk.2.isLt; omega
  by_cases left : sk.1.val ≤ 4
  · exact mateWithin_mono (top_left_bound hq ht hp top left) (by decide)
  have sx : sk.1.val = 5 := by
    have bound := sk.1.isLt
    have weakBound := wk.1.isLt
    have wy := hp.2.2.1
    have wx := hp.2.2.2
    simp only [dInf,absDiff] at hfar; omega
  let su : Square := (4,7)
  obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; have := hp.2.1; omega)
    (by simp only [dInf,absDiff,su]; have := hp.2.2.2; omega)
  have outside : OutsidePrison su := Or.inr (by decide)
  apply mateWithin_pair ht hl hc (prison_reply_exists hm hc hp outside)
  intro r hr
  obtain ⟨t,hmt,hrt,hpt⟩ := prison_reply hm hc hp outside hr
  exact top_left_bound hmt hrt hpt rfl (by decide)

end EndgameChess.Rules.KQK
