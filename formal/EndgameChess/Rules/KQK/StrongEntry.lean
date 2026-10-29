import EndgameChess.Rules.KQK.SameRankEntry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem positive_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 97 q := by
  by_cases same : qs.2.val = sk.2.val
  · exact same_rank_entry hq ht gap same hc
  · exact offrank_entry hq ht gap same hc

/-- Universal strong-turn KQK forcing with a sufficient 50-move budget.
No incoming weak check is the fresh-legal/arrival condition. -/
theorem strong_entry_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hc : inCheck q σ.opp = false) : MateWithin σ 97 q := by
  have far : 2 ≤ dInf sk wk := by
    have h0 : dInf sk wk ≠ 0 := fun h => hq.2.1 (dInf_eq_zero_iff.mp h)
    have h1 : dInf sk wk ≠ 1 := by
      intro near
      have check := (weak_check hq).mpr (Or.inl near)
      rw [hc] at check
      cases check
    omega
  by_cases up : sk.2.val+2 ≤ wk.2.val
  · exact positive_entry hq ht up hc
  by_cases down : wk.2.val+2 ≤ sk.2.val
  · apply unframe_bound reflectY hq
    apply positive_entry (framed_material reflectY hq) ht
    · dsimp [reflectY,symY]; omega
    · exact framed_weak_not_check reflectY hq hc
  by_cases right : sk.1.val+2 ≤ wk.1.val
  · apply unframe_bound swap hq
    exact positive_entry (framed_material swap hq) ht right (framed_weak_not_check swap hq hc)
  · apply unframe_bound anti hq
    apply positive_entry (framed_material anti hq) ht
    · dsimp [anti,symAnti]; simp only [dInf,absDiff] at far; omega
    · exact framed_weak_not_check anti hq hc

theorem strong_arrival_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (ha : ∃ p, Legal p q) : MateWithin σ 97 q := by
  obtain ⟨p,hl⟩ := ha
  have previous : p.turn = σ.opp := by rw [← ht,turn_of_legal hl,opp_opp]
  have hc := legal_mover_safe hl
  rw [previous] at hc
  exact strong_entry_bound hq ht hc

/-- A safe queen survives every legal weak reply. Stalemate is excluded
by the explicit nonempty-reply premise, rather than by vacuous defence. -/
theorem safe_weak_entry_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (safe : SafeQueen sk qs wk) (hne : ∃ r, Legal q r) : MateWithin σ 98 q := by
  apply mateWithin_defend ht hne
  intro r hr
  obtain ⟨t,hm,hrt,_,_,_⟩ := safe_reply hq ht safe hr
  exact strong_arrival_bound hm hrt ⟨q,hr⟩

end EndgameChess.Rules.KQK
