import EndgameChess.Rules.KQK.KnightPrison

/-! Finishing the two-square-height knight configuration without the
stalemating king advance. All bounds here are sufficient, not exact. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem left_corner_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 4) (qx : qs.1.val = 1) (qy : qs.2.val = 5)
    (wx : wk.1.val = 0) (wy : wk.2.val = 7) : MateWithin σ 31 q := by
  have hm : IsKQK (pos σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) q.turn)
      σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) :=
    ⟨reflectX.toBoardSym.ne_iff.mpr hq.1,reflectX.toBoardSym.ne_iff.mpr hq.2.1,
      reflectX.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  apply unframe_bound reflectX hq
  apply corner_knight_rescue hm ht
  all_goals dsimp [reflectX,symX]; omega

private theorem left_fork_weak_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (low : sk.2.val ≤ 4) (qx : qs.1.val = 1) (qy : qs.2.val = 5)
    (wx : wk.1.val = 1) (wy : wk.2.val = 7) : MateWithin σ 32 q := by
  have safe : SafeQueen sk qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
  have existsReply : ∃ r, Legal q r := by
    let t : Square := (0,7)
    obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hq ht
      (by simp only [dInf,absDiff,t]; omega)
      (by simp only [ne_iff_coords,t]; omega)
      (by simp only [dInf,absDiff,t]; omega)
      (by apply not_sees_of_not_line <;> simp only [absDiff,t] <;> omega)
    exact ⟨r,hr⟩
  apply mateWithin_defend ht existsReply
  intro r hr
  obtain ⟨t,hm,hrt,hd,hfar,hn⟩ := safe_reply hq ht safe hr
  have bx := t.1.isLt
  have by' := t.2.isLt
  have lower : 6 ≤ t.2.val := by simp only [dInf,absDiff] at hd; omega
  have notNear : ¬ dInf qs t = 1 := fun h => hn (near_sees h)
  have notFile : t.1.val ≠ 1 := by
    intro one
    apply hn
    apply rook_sees_queen
    refine ⟨⟨ne_iff_coords.mp hm.2.2.1,Or.inl (by omega)⟩,?_,not_onSeg_end _ _⟩
    simp only [OnSeg]; omega
  have points : t.2.val = 7 ∧ (t.1.val = 0 ∨ t.1.val = 2) := by
    simp only [dInf,absDiff] at hd notNear
    omega
  rcases points.2 with left | right
  · exact left_corner_bound hm hrt low qx qy left points.1
  · let nq : Square := (0,6)
    obtain ⟨c,hl,hmc,hct⟩ := queen_move (t := nq) hm hrt
      (near_sees (by simp only [dInf,absDiff,nq]; omega))
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega) hfar
    have wall : EdgeWall sk nq t := ⟨by omega,rfl,points.1,by decide,by dsimp [nq]; omega⟩
    exact mateWithin_mono (mateWithin_choose hrt hl (edge_wall_weak_bound hmc hct wall))
      (by decide)

/-- At file zero, shift the queen below the king first; the two resulting
top-rank replies have the reflected-corner or wide-corridor finish. -/
theorem left_knight_rescue {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 4) (qx : qs.1.val = 0) (qy : qs.2.val = 5)
    (wx : wk.1.val = 1) (wy : wk.2.val = 7) : MateWithin σ 33 q := by
  let nq : Square := (1,5)
  obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht
    (near_sees (by simp only [dInf,absDiff,nq]; omega))
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  exact mateWithin_choose ht hl (left_fork_weak_bound hm hc low rfl rfl wx wy)

/-- A knight offset above rank five is finished by widening the queen wall,
with boundary repairs at the two ends. Moving the king up can stalemate. -/
theorem rank_five_knight_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 4) (qy : qs.2.val = 5)
    (gap : qs.1.val+1 = wk.1.val) (wy : wk.2.val = 7) : MateWithin σ 33 q := by
  by_cases left : wk.1.val = 1
  · exact left_knight_rescue hq ht low (by omega) qy left wy
  by_cases right : wk.1.val = 7
  · exact mateWithin_mono (corner_knight_rescue hq ht low (by omega) qy right wy) (by decide)
  have wx : 2 ≤ wk.1.val ∧ wk.1.val ≤ 6 := by have bound := wk.1.isLt; omega
  let nq : Square := (⟨wk.1.val-2,by omega⟩,6)
  obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht
    (near_sees (by simp only [dInf,absDiff,nq]; omega))
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have wall : EdgeWall sk nq wk := ⟨by omega,rfl,wy,by dsimp [nq]; omega,by dsimp [nq]; omega⟩
  exact mateWithin_mono (mateWithin_choose ht hl (edge_wall_weak_bound hm hc wall)) (by decide)

/-- A queen on rank five can always check the top-right corner from file
five. The checking square itself is excluded because the queen must move. -/
theorem rank_five_corner_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.2.val ≤ 4) (qy : qs.2.val = 5) (qx : qs.1.val ≠ 5)
    (wx : wk.1.val = 7) (wy : wk.2.val = 7) : MateWithin σ 31 q := by
  let nq : Square := (5,5)
  have see : QueenSees qs nq sk wk := by
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inr (by dsimp [nq]; omega)⟩,?_,?_⟩
    · simp only [OnSeg,nq]; omega
    · simp only [OnSeg,nq]; omega
  obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  exact mateWithin_choose ht hl (knight_box_weak_bound hm hc low
    ⟨rfl,rfl,by omega,by omega⟩ (Or.inl (by simp only [dInf,absDiff,nq]; omega)))

end EndgameChess.Rules.KQK
