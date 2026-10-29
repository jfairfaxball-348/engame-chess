import EndgameChess.Rules.KQK.ShadowExit

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- Copy the lone king's step with the queen, retaining its knight offset.
The weighted potential supplies a uniform bound for every defence. -/
theorem shadow_weak_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hs : Shadow sk qs wk) (hx : wk.1.val ≤ 6) :
    MateWithin σ (2*shadowPotential wk+28) q := by
  generalize hp : shadowPotential wk = p
  induction p using Nat.strongRecOn generalizing q qs wk with
  | ind p ih =>
    change MateWithin σ (2*p+27+1) q
    apply mateWithin_defend ht (shadow_reply_exists hq ht hs hx)
    intro r hr
    obtain ⟨t,hm,hrt,hd,hfar,tx,sum,decrease,exit⟩ := shadow_reply hq ht hs hx hr
    by_cases edge : t.1.val = 7
    · obtain ⟨qx,off⟩ := exit edge
      have he : ShadowExit sk qs t := ⟨hs.1,qx,edge,off⟩
      exact mateWithin_mono (shadow_exit_bound hm hrt he) (by omega)
    · have x6 : t.1.val ≤ 6 := by have bound := t.1.isLt; omega
      have x1 : 1 ≤ t.1.val := by have oldX := hs.2.2.1; omega
      have high : 8 ≤ t.1.val+t.2.val := by have oldHigh := hs.2.1; omega
      have y2 : 2 ≤ t.2.val := by omega
      let nq : Square := (⟨t.1.val-1,by omega⟩,⟨t.2.val-2,by have := t.2.isLt; omega⟩)
      have queenStep : dInf qs nq = 1 := by
        have oldX := hs.2.2.1
        have oldY := hs.2.2.2
        simp only [dInf,absDiff,nq] at hd ⊢; omega
      have neKing : nq ≠ sk := by
        have low := hs.1
        simp only [ne_iff_coords,nq]; omega
      have neWeak : nq ≠ t := by simp only [ne_iff_coords,nq]; omega
      obtain ⟨c,hl,hmq,hc⟩ := queen_move (t := nq) hm hrt
        (near_sees queenStep) neKing neWeak hfar
      have shadow : Shadow sk nq t :=
        ⟨hs.1,high,by dsimp [nq]; omega,by dsimp [nq]; omega⟩
      have smaller : shadowPotential t < p := by omega
      have result := ih (shadowPotential t) smaller hmq hc shadow x6 rfl
      exact mateWithin_mono (mateWithin_choose hrt hl result) (by omega)

theorem shadow_weak_fifty_two {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hs : Shadow sk qs wk) (hx : wk.1.val ≤ 6) : MateWithin σ 52 q := by
  have bound : shadowPotential wk ≤ 12 := by
    have x1 := hs.2.2.1
    have high := hs.2.1
    simp only [shadowPotential]; omega
  exact mateWithin_mono (shadow_weak_bound hq ht hs hx) (by omega)

/-- A harmless king tempo starts the copying strategy. The result concerns
the stated geometric region, not all strong-turn KQK positions. -/
theorem shadow_strong_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hs : Shadow sk qs wk) (hx : wk.1.val ≤ 6) : MateWithin σ 53 q := by
  let su : Square := if h : 0 < sk.1.val then (⟨sk.1.val-1,by have := sk.1.isLt; omega⟩,sk.2)
    else if h : 0 < sk.2.val then (sk.1,⟨sk.2.val-1,by have := sk.2.isLt; omega⟩)
    else (1,0)
  have low : su.1.val+su.2.val ≤ 4 := by
    have oldLow := hs.1
    dsimp [su]; split <;> (try split) <;> dsimp <;> omega
  have step : dInf sk su = 1 := by
    dsimp [su]; split <;> (try split) <;> simp only [dInf,absDiff] <;> omega
  have ne : su ≠ qs := by
    have high := hs.2.1
    have qx := hs.2.2.1
    have qy := hs.2.2.2
    simp only [ne_iff_coords]; omega
  obtain ⟨c,hl,hm,hc⟩ := king_move hq ht step ne (sum_far low hs.2.1)
  exact mateWithin_choose ht hl (shadow_weak_fifty_two hm hc ⟨low,hs.2⟩ hx)

end EndgameChess.Rules.KQK
