import EndgameChess.Rules.KQK.EntryGeometry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem king_blocks_target_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (kx : sk.1.val = 5) (ky : sk.2.val = 5)
    (qx : qs.1.val = 6) (qy : qs.2.val = 5)
    (wx : wk.1.val = 7) (wy : wk.2.val = 7) : MateWithin σ 3 q := by
  let nq : Square := (7,5)
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht
    (near_sees (by simp only [dInf,absDiff,nq]; omega))
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
  have hne : ∃ r, Legal c r := by
    let t : Square := (6,7)
    obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
      (by simp only [dInf,absDiff,t]; omega)
      (by decide)
      (by simp only [dInf,absDiff,t]; omega)
      (by apply not_sees_of_not_line <;> decide)
    exact ⟨r,hr⟩
  apply mateWithin_pair ht hl hct hne
  intro r hr
  obtain ⟨t,hmt,hrt,hd,hfar,hn⟩ := safe_reply hm hct safe hr
  have bx := t.1.isLt
  have by' := t.2.isLt
  have notNear : ¬ dInf nq t = 1 := fun h => hn (near_sees h)
  have point : t.1.val = 6 ∧ t.2.val = 7 := by
    simp only [dInf,absDiff,nq] at hd notNear
    omega
  let lastQ : Square := (6,6)
  obtain ⟨u,hu,hum,hut⟩ := queen_move (t := lastQ) hmt hrt (near_sees (by decide))
    (by simp only [ne_iff_coords,lastQ]; omega)
    (by simp only [ne_iff_coords,lastQ]; omega) hfar
  apply mateWithin_choose hrt hu
  exact ⟨hut,edge_mated hum hut point.2 (by dsimp [lastQ]; omega) rfl
    (by simp only [dInf,absDiff,lastQ]; omega)⟩

/-- Repair the corner knight trap even when the strong king shares the
queen's rank. If it occupies the usual checking target, use the other check. -/
theorem corner_knight_low_five_rescue {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 5) (qx : qs.1.val = 6) (qy : qs.2.val = 5)
    (wx : wk.1.val = 7) (wy : wk.2.val = 7) : MateWithin σ 33 q := by
  by_cases blocked : sk.1.val = 5 ∧ sk.2.val = 5
  · exact mateWithin_mono (king_blocks_target_bound hq ht blocked.1 blocked.2 qx qy wx wy) (by decide)
  let nq : Square := (5,5)
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht
    (near_sees (by simp only [dInf,absDiff,nq]; omega))
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
  have hne : ∃ r, Legal c r := by
    let t : Square := (6,7)
    obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
      (by simp only [dInf,absDiff,t]; omega)
      (by decide)
      (by simp only [dInf,absDiff,t]; omega)
      (by apply not_sees_of_not_line <;> decide)
    exact ⟨r,hr⟩
  apply mateWithin_pair ht hl hct hne
  intro r hr
  obtain ⟨t,hmt,hrt,hd,_,hn⟩ := safe_reply hm hct safe hr
  have bx := t.1.isLt
  have by' := t.2.isLt
  have notNear : ¬ dInf nq t = 1 := fun h => hn (near_sees h)
  have points : (t.1.val = 6 ∧ t.2.val = 7) ∨ (t.1.val = 7 ∧ t.2.val = 6) := by
    simp only [dInf,absDiff,nq] at hd notNear
    omega
  exact knight_prison_low_five_bound hmt hrt low ⟨rfl,rfl,points⟩

end EndgameChess.Rules.KQK
