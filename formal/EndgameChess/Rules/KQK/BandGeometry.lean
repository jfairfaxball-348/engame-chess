import EndgameChess.Rules.KQK.EdgeEntry

/-! A separating rank with the king below it. Local escape witnesses work
on the whole board, except the excluded one-cell corner prison. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def Wall (sk qs wk : Square) : Prop :=
  sk.2.val < qs.2.val ∧ qs.2.val < wk.2.val ∧ qs.1.val < wk.1.val

def OpenBand (qs : Square) : Prop :=
  qs.2.val ≤ 4 ∨ (qs.2.val = 5 ∧ qs.1.val ≤ 5)

private theorem box_reply_at {q : Position} {σ : Colour} {sk qs wk t : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (below : sk.2.val < qs.2.val) (step : dInf wk t = 1)
    (right : qs.1.val < t.1.val) (above : qs.2.val < t.2.val)
    (diagonal : t.1.val+qs.2.val ≠ qs.1.val+t.2.val) : ∃ r, Legal q r := by
  have ne : t ≠ qs := by simp only [ne_iff_coords]; omega
  have far : 2 ≤ dInf sk t := by simp only [dInf,absDiff]; omega
  have unseen : ¬ QueenSees qs t sk t := by
    apply not_sees_of_not_line <;> (try simp only [absDiff]) <;> omega
  obtain ⟨r,hr,_,_⟩ := weak_move hq ht step ne far unseen
  exact ⟨r,hr⟩

/-- In an upper-right queen box, a king strictly below the queen cannot
remove the escape witness. The excluded top-right knight prison is the
only obstruction at queen rank five. -/
theorem wall_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (wall : Wall sk qs wk) (band : OpenBand qs) : ∃ r, Legal q r := by
  obtain ⟨below,above,right⟩ := wall
  have qy : qs.2.val ≤ 5 := by rcases band with low | ⟨five,_⟩ <;> omega
  have wxBound := wk.1.isLt
  have wyBound := wk.2.isLt
  by_cases up : wk.2.val < 7
  · by_cases diagonal : wk.1.val+qs.2.val = qs.1.val+(wk.2.val+1)
    · by_cases down : qs.2.val+2 ≤ wk.2.val
      · let t : Square := (wk.1,⟨wk.2.val-1,by omega⟩)
        apply box_reply_at (t := t) hq ht below
        · simp only [dInf,absDiff,t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega
      · have wy : wk.2.val = qs.2.val+1 := by omega
        have wx : wk.1.val = qs.1.val+2 := by omega
        by_cases room : wk.1.val < 7
        · let t : Square := (⟨wk.1.val+1,by omega⟩,wk.2)
          apply box_reply_at (t := t) hq ht below
          · simp only [dInf,absDiff,t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
        · have edge : wk.1.val = 7 := by omega
          let t : Square := (6,⟨wk.2.val+1,by omega⟩)
          apply box_reply_at (t := t) hq ht below
          · simp only [dInf,absDiff,t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
    · let t : Square := (wk.1,⟨wk.2.val+1,by omega⟩)
      apply box_reply_at (t := t) hq ht below
      · simp only [dInf,absDiff,t]; omega
      · dsimp [t]; omega
      · dsimp [t]; omega
      · dsimp [t]; omega
  · have top : wk.2.val = 7 := by omega
    by_cases room : wk.1.val < 7
    · by_cases diagonal : wk.1.val+1+qs.2.val = qs.1.val+7
      · by_cases gap : qs.1.val+2 ≤ wk.1.val
        · let t : Square := (⟨wk.1.val-1,by omega⟩,7)
          apply box_reply_at (t := t) hq ht below
          · simp only [dInf,absDiff,t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
        · have near : wk.1.val = qs.1.val+1 := by omega
          have five : qs.2.val = 5 := by omega
          let t : Square := (⟨wk.1.val+1,by omega⟩,6)
          apply box_reply_at (t := t) hq ht below
          · simp only [dInf,absDiff,t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
          · dsimp [t]; omega
      · let t : Square := (⟨wk.1.val+1,by omega⟩,7)
        apply box_reply_at (t := t) hq ht below
        · simp only [dInf,absDiff,t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega
    · have edge : wk.1.val = 7 := by omega
      by_cases diagonal : 7+qs.2.val = qs.1.val+6
      · have low : qs.2.val ≤ 4 := by rcases band with low | ⟨five,qx⟩ <;> omega
        let t : Square := (6,7)
        apply box_reply_at (t := t) hq ht below
        · simp only [dInf,absDiff,t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega
      · let t : Square := (7,6)
        apply box_reply_at (t := t) hq ht below
        · simp only [dInf,absDiff,t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega
        · dsimp [t]; omega

/-- A file margin of three gives an escape at every queen rank, including
rank six. This is the margin retained by the general entry construction. -/
theorem wall_far_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (wall : Wall sk qs wk) (gap : qs.1.val+3 ≤ wk.1.val) : ∃ r, Legal q r := by
  obtain ⟨below,above,_⟩ := wall
  by_cases diagonal : wk.1.val-1+qs.2.val = qs.1.val+wk.2.val
  · by_cases room : wk.1.val < 7
    · let t : Square := (⟨wk.1.val+1,by omega⟩,wk.2)
      apply box_reply_at (t := t) hq ht below
      · simp only [dInf,absDiff,t]; omega
      · dsimp [t]; omega
      · dsimp [t]; omega
      · dsimp [t]; omega
    · have wx : wk.1.val = 7 := by have bound := wk.1.isLt; omega
      let t : Square := (wk.1,⟨wk.2.val-1,by have bound := wk.2.isLt; omega⟩)
      apply box_reply_at (t := t) hq ht below
      · simp only [dInf,absDiff,t]; omega
      · dsimp [t]; omega
      · dsimp [t]; omega
      · dsimp [t]; omega
  · let t : Square := (⟨wk.1.val-1,by have bound := wk.1.isLt; omega⟩,wk.2)
    apply box_reply_at (t := t) hq ht below
    · simp only [dInf,absDiff,t]; omega
    · dsimp [t]; omega
    · dsimp [t]; omega
    · dsimp [t]; omega

theorem wall_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (wall : Wall sk qs wk) (safe : SafeQueen sk qs wk) (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ Wall sk qs t ∧
      dInf wk t = 1 ∧ ¬ QueenSees qs t sk t ∧ inCheck r σ.opp = false := by
  obtain ⟨below,above,right⟩ := wall
  obtain ⟨t,hm,hrt,hd,_,hn⟩ := safe_reply hq ht safe hl
  have ty := rook_rank_barrier below above hd (Ne.symm hm.2.2.1)
    (fun h => hn (rook_sees_queen h))
  have tx : qs.1.val < t.1.val := by
    by_cases strict : qs.1.val < t.1.val
    · exact strict
    · have equal : t.1.val = qs.1.val := by simp only [dInf,absDiff] at hd; omega
      apply False.elim
      apply hn
      apply rook_sees_queen
      refine ⟨⟨by omega,Or.inl equal.symm⟩,?_,not_onSeg_end _ _⟩
      simp only [OnSeg]; omega
  have notCheck := legal_mover_safe hl
  rw [ht] at notCheck
  exact ⟨t,hm,hrt,⟨below,ty,tx⟩,hd,hn,notCheck⟩

end EndgameChess.Rules.KQK
