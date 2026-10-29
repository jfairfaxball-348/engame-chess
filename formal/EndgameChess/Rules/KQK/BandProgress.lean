import EndgameChess.Rules.KQK.RankFive

/-! Monotone progress along a separating queen rank. The king walks towards
the weak file; queen preparation advances its file and preserves the king
on the inside. The subsequent rank advance is a separate obligation. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

structure Prepared (sk qs wk : Square) : Prop where
  wall : Wall sk qs wk
  top : qs.2.val ≤ 5
  kingRank : sk.2.val+1 = qs.2.val
  queenLeft : qs.1.val ≤ sk.1.val
  kingLeft : sk.1.val ≤ wk.1.val

def bandPotential (sk qs : Square) : Nat :=
  2*(7-sk.1.val)+2*(7-qs.1.val)+4*(5-qs.2.val)

private theorem prepared_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hp : Prepared sk qs wk) (safe : SafeQueen sk qs wk)
    (control : sk.1.val ≤ qs.1.val+1 ∨ sk.1.val+1 ≤ wk.1.val)
    (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ Prepared sk qs t ∧
      inCheck r σ.opp = false := by
  obtain ⟨t,hm,hrt,wall,hd,_,hc⟩ := wall_reply hq ht hp.wall safe hl
  have kingLeft : sk.1.val ≤ t.1.val := by
    rcases control with near | behind
    · have right := wall.2.2; omega
    · simp only [dInf,absDiff] at hd; omega
  exact ⟨t,hm,hrt,⟨wall,hp.top,hp.kingRank,hp.queenLeft,kingLeft⟩,hc⟩

private theorem prepared_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hp : Prepared sk qs wk)
    (notTrap : qs.2.val < 5 ∨ qs.1.val < 6 ∨ wk.2.val < 7) : ∃ r, Legal q r := by
  by_cases band : OpenBand qs
  · exact wall_reply_exists hq ht hp.wall band
  have qy : qs.2.val = 5 := by
    by_cases low : qs.2.val ≤ 4
    · exact False.elim (band (Or.inl low))
    · have top := hp.top; omega
  have qx : qs.1.val = 6 := by
    have right := hp.wall.2.2
    have bound := wk.1.isLt
    by_cases low : qs.1.val ≤ 5
    · exact False.elim (band (Or.inr ⟨qy,low⟩))
    · omega
  have wx : wk.1.val = 7 := by have right := hp.wall.2.2; have bound := wk.1.isLt; omega
  have wy : wk.2.val = 6 := by
    have above := hp.wall.2.1
    rcases notTrap with low | left | down <;> omega
  have ky : sk.2.val = 4 := by have rank := hp.kingRank; omega
  let t : Square := (7,7)
  obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hq ht
    (by simp only [dInf,absDiff,t]; omega)
    (by simp only [ne_iff_coords,t]; omega)
    (by simp only [dInf,absDiff,t]; omega)
    (by apply not_sees_of_not_line <;> simp only [absDiff,t] <;> omega)
  exact ⟨r,hr⟩

/-- A horizontal king pursuit costs one defended pair and decreases the
potential by at least two, with no reset of either file. -/
theorem prepared_king_step {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prepared sk qs wk) (hc : inCheck q σ.opp = false)
    (gap : sk.1.val+2 ≤ wk.1.val) :
    ∃ c su, Legal q c ∧ IsKQK c σ su qs wk ∧ c.turn = σ.opp ∧
      (∃ r, Legal c r) ∧
      (∀ r, Legal c r → ∃ t, IsKQK r σ su qs t ∧ r.turn = σ ∧
        Prepared su qs t ∧ inCheck r σ.opp = false) ∧
      bandPotential su qs+2 ≤ bandPotential sk qs := by
  have wxBound := wk.1.isLt
  let su : Square := (⟨sk.1.val+1,by omega⟩,sk.2)
  have rank := hp.kingRank
  have qLeft := hp.queenLeft
  have above := hp.wall.2.1
  obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; omega)
    (by simp only [dInf,absDiff,su]; omega)
  have next : Prepared su qs wk := by
    refine ⟨⟨?_,above,hp.wall.2.2⟩,hp.top,rank,?_,?_⟩ <;> dsimp [su] <;> omega
  have openBand : OpenBand qs := by
    by_cases low : qs.2.val ≤ 4
    · exact Or.inl low
    · exact Or.inr ⟨by have top := hp.top; omega,by omega⟩
  have safe : SafeQueen su qs wk := Or.inl (queen_distant_of_not_check hq hc)
  refine ⟨c,su,hl,hm,hct,wall_reply_exists hm hct next.wall openBand,?_,?_⟩
  · intro r hr
    exact prepared_reply hm hct next safe (Or.inr (by dsimp [su]; omega)) hr
  · simp only [bandPotential,su]; omega

/-- Move the queen towards the weak file while the king is within one
file behind it. The target is protected. A top-right rank-five trap must
be finished by the corner repair instead. -/
theorem prepared_queen_step {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prepared sk qs wk) (close : wk.1.val ≤ sk.1.val+1)
    (gap : qs.1.val+2 ≤ wk.1.val)
    (notCorner : qs.2.val < 5 ∨ wk.2.val < 7 ∨ wk.1.val < 7) :
    ∃ c nq, Legal q c ∧ IsKQK c σ sk nq wk ∧ c.turn = σ.opp ∧
      (∃ r, Legal c r) ∧
      (∀ r, Legal c r → ∃ t, IsKQK r σ sk nq t ∧ r.turn = σ ∧
        Prepared sk nq t ∧ inCheck r σ.opp = false) ∧
      bandPotential sk nq+2 ≤ bandPotential sk qs := by
  let nq : Square := (⟨wk.1.val-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩,qs.2)
  have below := hp.wall.1
  have above := hp.wall.2.1
  have kingLeft := hp.kingLeft
  have rank := hp.kingRank
  have wxBound := wk.1.isLt
  have see : QueenSees qs nq sk wk := by
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inr rfl⟩,?_,?_⟩
    · simp only [OnSeg,nq]; omega
    · simp only [OnSeg,nq]; omega
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have next : Prepared sk nq wk := by
    refine ⟨⟨below,above,?_⟩,hp.top,rank,?_,kingLeft⟩ <;> dsimp [nq] <;> omega
  have safe : SafeQueen sk nq wk := Or.inr (by simp only [dInf,absDiff,nq]; omega)
  have notTrap : nq.2.val < 5 ∨ nq.1.val < 6 ∨ wk.2.val < 7 := by
    rcases notCorner with low | down | left
    · exact Or.inl low
    · exact Or.inr (Or.inr down)
    · exact Or.inr (Or.inl (by dsimp [nq]; omega))
  refine ⟨c,nq,hl,hm,hct,prepared_reply_exists hm hct next notTrap,?_,?_⟩
  · intro r hr
    exact prepared_reply hm hct next safe (Or.inl (by dsimp [nq]; omega)) hr
  · simp only [bandPotential,nq]; omega

end EndgameChess.Rules.KQK
