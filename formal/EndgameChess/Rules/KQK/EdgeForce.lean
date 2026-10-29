import EndgameChess.Rules.KQK.Edge

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

theorem corner_prison_fifteen {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : CornerPrison sk qs wk) : MateWithin σ 15 q := by
  have hd : dInf sk escort ≤ 7 := by
    have hx := sk.1.isLt
    have hy := sk.2.isLt
    simp only [dInf,absDiff,escort]; omega
  exact mateWithin_mono (corner_prison_bound hq ht hp) (by omega)

private theorem shift_queen {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ) (he : EdgeWall sk qs wk)
    (x : Fin 8) (hne : x.val ≠ qs.1.val) :
    ∃ r, Legal q r ∧ IsKQK r σ sk (x,6) wk ∧ r.turn = σ.opp := by
  obtain ⟨hsk,hqY,hwY,hqX,hwX⟩ := he
  apply queen_move (t := (x,6)) hq ht
  · apply rook_sees_queen
    refine ⟨⟨?_,Or.inr hqY⟩,?_,?_⟩
    · intro e; exact hne e.1.symm
    · simp only [OnSeg]; omega
    · simp only [OnSeg]; omega
  · simp only [ne_iff_coords]; omega
  · simp only [ne_iff_coords]; omega
  · simp only [dInf,absDiff]; omega

private theorem front_setup {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : EdgeWall sk qs wk) (hw : wk.1.val ≤ 5) :
    ∃ c sk' qs', Legal q c ∧ IsKQK c σ sk' qs' wk ∧ c.turn = σ.opp ∧
      EdgeWall sk' qs' wk ∧ qs'.1.val+2 = wk.1.val := by
  by_cases close : qs.1.val+2 = wk.1.val
  · let y : Nat := if sk.2.val = 0 then 1 else sk.2.val-1
    have hy : y ≤ 5 ∧ absDiff sk.2.val y = 1 := by
      have hsk := he.1
      dsimp [y]; split <;> simp only [absDiff] <;> omega
    let su : Square := (sk.1,⟨y,by omega⟩)
    have step : dInf sk su = 1 := by simp only [dInf,absDiff,su] at hy ⊢; omega
    have ne : su ≠ qs := by
      have hqy := he.2.1
      simp only [ne_iff_coords,su]; omega
    have far : 2 ≤ dInf su wk := by
      have hwy := he.2.2.1
      simp only [dInf,absDiff,su]; omega
    obtain ⟨c,hl,hm,hc⟩ := king_move hq ht step ne far
    exact ⟨c,su,qs,hl,hm,hc,⟨hy.1,he.2⟩,close⟩
  · let x : Fin 8 := ⟨wk.1.val-2,by omega⟩
    have nx : x.val ≠ qs.1.val := by have hx := he.2.2.2.2; dsimp [x]; omega
    obtain ⟨c,hl,hm,hc⟩ := shift_queen hq ht he x nx
    have hx : x.val+2 = wk.1.val := by have hx := he.2.2.2.2; dsimp [x]; omega
    refine ⟨c,sk,(x,6),hl,hm,hc,?_,hx⟩
    exact ⟨he.1,rfl,he.2.2.1,by dsimp [x]; omega,by dsimp [x]; omega⟩

/-- Protected/distant queen wall on the last two ranks: approach and check
force mate. The bound is deliberately loose and not an exact mate count. -/
theorem edge_wall_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : EdgeWall sk qs wk) :
    MateWithin σ (2*(6-wk.1.val)+17) q := by
  generalize hn : 6-wk.1.val = n
  induction n using Nat.strongRecOn generalizing q sk qs wk with
  | ind n ih =>
    by_cases done : 6 ≤ wk.1.val
    · have bound : MateWithin σ 17 q := by
        by_cases already : qs.1.val = 4
        · exact mateWithin_mono (corner_prison_fifteen hq ht ⟨he,already⟩) (by decide)
        · obtain ⟨c,hl,hm,hc⟩ := shift_queen hq ht he 4 (Ne.symm already)
          have newWall : EdgeWall sk (4,6) wk := ⟨he.1,rfl,he.2.2.1,by decide,done⟩
          have hne := edge_reply_exists hm hc newWall
          have hall : ∀ r, Legal c r → MateWithin σ 15 r := by
            intro r hr
            obtain ⟨t,hmt,hrt,het,step⟩ := edge_reply hm hc newWall hr
            exact corner_prison_fifteen hmt hrt ⟨het,rfl⟩
          exact mateWithin_pair ht hl hc hne hall
      exact mateWithin_mono bound (by omega)
    · have small : wk.1.val ≤ 5 := by omega
      obtain ⟨c,su,nq,hl,hm,hc,newWall,front⟩ := front_setup hq ht he small
      have hne := edge_reply_exists hm hc newWall
      have hall : ∀ r, Legal c r → MateWithin σ (2*(n-1)+17) r := by
        intro r hr
        obtain ⟨t,hmt,hrt,het,step⟩ := edge_reply hm hc newWall hr
        have next : t.1.val = wk.1.val+1 := by
          have oldY := newWall.2.2.1
          have newY := het.2.2.1
          have newX := het.2.2.2.2
          simp only [dInf,absDiff] at step
          omega
        have decrease : 6-t.1.val < n := by omega
        have cost : 6-t.1.val = n-1 := by omega
        have result := ih (6-t.1.val) decrease hmt hrt het rfl
        rwa [cost] at result
      have result := mateWithin_pair ht hl hc hne hall
      have cost : 2*(n-1)+17+2 = 2*n+17 := by omega
      rwa [cost] at result

theorem edge_wall_twenty_five {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : EdgeWall sk qs wk) : MateWithin σ 25 q := by
  have hx := he.2.2.2.2
  exact mateWithin_mono (edge_wall_bound hq ht he) (by omega)

end EndgameChess.Rules.KQK
