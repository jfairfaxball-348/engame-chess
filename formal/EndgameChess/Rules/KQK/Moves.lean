import EndgameChess.Rules.KQK.Basic

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

theorem queen_move {q : Position} {σ : Colour} {sk qs wk t : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hsee : QueenSees qs t sk wk) (hts : t ≠ sk) (htw : t ≠ wk)
    (hfar : 2 ≤ dInf sk wk) :
    ∃ r, Legal q r ∧ IsKQK r σ sk t wk ∧ r.turn = σ.opp := by
  obtain ⟨h12,h13,h23,hb⟩ := hq
  let m : Move := ⟨qs,t,none⟩
  have hsrc : q.board m.src = some ⟨q.turn,.queen⟩ := by
    rw [hb,ht]; exact LoneKing.board_xs h12
  have htr : t ≠ qs := by
    intro e; subst e
    rcases hsee.1 with h | h
    · simp [diagGeom] at h
    · exact h.1 ⟨rfl,rfl⟩
  have hdst : q.board m.dst = none := by
    rw [hb]; exact LoneKing.board_none.mpr ⟨hts,htr,htw⟩
  have hatt : attacksFrom q.board ⟨q.turn,.queen⟩ m.src m.dst = true := by
    rw [hb,ht]; exact queen_attacks.mpr hsee
  have hp : isPseudo q m = true := by
    unfold isPseudo; rw [hsrc]; simp [targetOK,hdst,hatt,m]
  have hb' : (play q m).board = queenBoard σ sk t wk := by
    rw [play_board_simple hsrc (by decide) rfl (by intro h; cases h)]
    funext x
    show (if x = t then some ⟨q.turn,.queen⟩ else if x = qs then none else q.board x) = _
    rw [hb,ht]; unfold queenBoard LoneKing.board
    by_cases e1 : x = t
    · subst e1; simp [hts]
    · by_cases e2 : x = qs
      · subst e2; simp [e1,Ne.symm h12,h23]
      · simp [e1,e2]
  have hm : IsKQK (play q m) σ sk t wk := ⟨Ne.symm hts,h13,htw,hb'⟩
  have hc : inCheck (play q m) q.turn = false := by
    rw [ht]
    cases he : inCheck (play q m) σ
    · rfl
    · have hh := (strong_check hm).mp he
      rw [dInf_comm] at hh; omega
  exact ⟨play q m,legal_of_pseudo hp hc,hm,by rw [play_turn,ht]⟩

theorem king_move {q : Position} {σ : Colour} {sk qs wk t : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hd : dInf sk t = 1) (htq : t ≠ qs) (hfar : 2 ≤ dInf t wk) :
    ∃ r, Legal q r ∧ IsKQK r σ t qs wk ∧ r.turn = σ.opp := by
  obtain ⟨h12,h13,h23,hb⟩ := hq
  let m : Move := ⟨sk,t,none⟩
  have hsrc : q.board m.src = some ⟨q.turn,.king⟩ := by
    rw [hb,ht]; exact LoneKing.board_sk
  have hts : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have htw : t ≠ wk := ne_of_dInf_pos (by omega)
  have hdst : q.board m.dst = none := by
    rw [hb]; exact LoneKing.board_none.mpr ⟨hts,htq,htw⟩
  have hp : isPseudo q m = true := by
    rw [isPseudo_of_king hsrc]
    have hg := kingGeom_iff.mpr hd
    simp [targetOK,hdst,hg,m]
  have hb' : (play q m).board = queenBoard σ t qs wk := by
    rw [play_board_simple hsrc (by decide) rfl (fun _ => hd)]
    funext x
    show (if x = t then some ⟨q.turn,.king⟩ else if x = sk then none else q.board x) = _
    rw [hb,ht]; unfold queenBoard LoneKing.board
    by_cases e1 : x = t
    · subst e1; simp
    · by_cases e2 : x = sk
      · subst e2; simp [e1,h12,h13]
      · simp [e1,e2]
  have hm : IsKQK (play q m) σ t qs wk := ⟨htq,htw,h23,hb'⟩
  have hc : inCheck (play q m) q.turn = false := by
    rw [ht]
    cases he : inCheck (play q m) σ
    · rfl
    · have hh := (strong_check hm).mp he
      rw [dInf_comm] at hh; omega
  exact ⟨play q m,legal_of_pseudo hp hc,hm,by rw [play_turn,ht]⟩

theorem weak_move {q : Position} {σ : Colour} {sk qs wk t : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hd : dInf wk t = 1) (htq : t ≠ qs) (hfar : 2 ≤ dInf sk t)
    (hn : ¬ QueenSees qs t sk t) :
    ∃ r, Legal q r ∧ IsKQK r σ sk qs t ∧ r.turn = σ := by
  obtain ⟨h12,h13,h23,hb⟩ := hq
  let m : Move := ⟨wk,t,none⟩
  have hsrc : q.board m.src = some ⟨q.turn,.king⟩ := by
    rw [hb,ht]; exact LoneKing.board_wk h13 h23
  have hts : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have htw : t ≠ wk := Ne.symm (ne_of_dInf_pos (by omega))
  have hdst : q.board m.dst = none := by
    rw [hb]; exact LoneKing.board_none.mpr ⟨hts,htq,htw⟩
  have hp : isPseudo q m = true := by
    rw [isPseudo_of_king hsrc]
    have hg := kingGeom_iff.mpr hd
    simp [targetOK,hdst,hg,m]
  have hb' : (play q m).board = queenBoard σ sk qs t := by
    rw [play_board_simple hsrc (by decide) rfl (fun _ => hd)]
    funext x
    show (if x = t then some ⟨q.turn,.king⟩ else if x = wk then none else q.board x) = _
    rw [hb,ht]; unfold queenBoard LoneKing.board
    by_cases e1 : x = t
    · subst e1; simp [hts,htq]
    · by_cases e2 : x = wk
      · subst e2; simp [e1,Ne.symm h13,Ne.symm h23]
      · simp [e1,e2]
  have hm : IsKQK (play q m) σ sk qs t := ⟨h12,Ne.symm hts,Ne.symm htq,hb'⟩
  have hc : inCheck (play q m) q.turn = false := by
    rw [ht]
    cases he : inCheck (play q m) σ.opp
    · rfl
    · rcases (weak_check hm).mp he with hh | hh
      · omega
      · exact False.elim (hn hh)
  exact ⟨play q m,legal_of_pseudo hp hc,hm,by rw [play_turn,ht,opp_opp]⟩

end EndgameChess.Rules.KQK
