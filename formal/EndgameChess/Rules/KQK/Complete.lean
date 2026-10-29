import EndgameChess.Rules.KQK.Moves
import EndgameChess.Rules.KRKForcing.OrdinaryMoves

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- Completeness of strong-turn ordinary moves, used for strategy transport. -/
theorem strong_reply {q r : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKQK q σ sk rs wk) (ht : q.turn = σ) (hn : q.castling = noRights)
    (hl : Legal q r) :
    (∃ t, IsKQK r σ t rs wk ∧ r.turn = σ.opp ∧
      dInf sk t = 1 ∧ t ≠ rs ∧ 2 ≤ dInf t wk) ∨
    (∃ t, IsKQK r σ sk t wk ∧ r.turn = σ.opp ∧
      QueenSees rs t sk wk ∧ t ≠ sk ∧ t ≠ wk ∧ 2 ≤ dInf sk wk) := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  obtain ⟨m, hm, rfl⟩ := hl
  have hp : isPseudo q m = true := by
    unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  have hc := not_inCheck_after_legal hm
  rw [ht] at hc
  obtain ⟨pc, hpc, hcol⟩ := own_of_isPseudo hp
  rw [hb] at hpc
  rcases LoneKing.board_some hpc with ⟨esrc, rfl⟩ | ⟨esrc, rfl⟩ | ⟨_, rfl⟩
  · have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by rw [hb, ht, esrc]; exact LoneKing.board_sk
    rw [isPseudo_of_king hsrc, canCastle_noRights hn] at hp
    simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    obtain ⟨htg, hpro, hg⟩ := hp
    have hd : dInf sk m.dst = 1 := by rw [← esrc]; exact kingGeom_iff.1 hg
    have hds : m.dst ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
    have hdr : m.dst ≠ rs := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact LoneKing.board_xs h12)).1
      exact this (by rw [ht])
    have hdw : m.dst ≠ wk := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact LoneKing.board_wk h13 h23)).2
      exact this rfl
    have hbp := play_board_simple hsrc (by decide) hpro (fun _ => by rw [esrc]; exact hd)
    have hb' : (play q m).board = LoneKing.board .queen σ m.dst rs wk := by
      rw [hbp]; funext x; rw [hb, ht, esrc]; unfold LoneKing.board
      by_cases e1 : x = m.dst
      · subst e1; simp
      · by_cases e2 : x = sk
        · subst e2; simp [e1, h12, h13]
        · simp [e1, e2]
    have hfar : 2 ≤ dInf m.dst wk := by
      have h0 : dInf m.dst wk ≠ 0 := fun h => hdw (dInf_eq_zero_iff.1 h)
      have h1 : dInf m.dst wk ≠ 1 := by
        intro h
        have := (strong_check ⟨hdr,hdw,h23,hb'⟩).2 (by rwa [dInf_comm])
        rw [this] at hc; cases hc
      omega
    exact Or.inl ⟨m.dst,⟨hdr,hdw,h23,hb'⟩,by simp [play_turn,ht],hd,hdr,hfar⟩
  · have hsrc : q.board m.src = some ⟨q.turn, .queen⟩ := by rw [hb, ht, esrc]; exact LoneKing.board_xs h12
    have hp' := hp
    unfold isPseudo at hp'
    rw [hsrc] at hp'
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at hp'
    obtain ⟨htg, hpro, hatt⟩ := hp'
    have hsee : QueenSees rs m.dst sk wk := by
      rw [hb, ht, esrc] at hatt
      exact queen_attacks.mp hatt
    have hds : m.dst ≠ sk := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact LoneKing.board_sk)).2
      exact this rfl
    have hdr : m.dst ≠ rs := by
      intro e
      rcases hsee.1 with diag | line
      · rw [e] at diag; simp [diagGeom] at diag
      · exact line.1 (by rw [e]; exact ⟨rfl,rfl⟩)
    have hdw : m.dst ≠ wk := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact LoneKing.board_wk h13 h23)).2
      exact this rfl
    have hbp := play_board_simple hsrc (by decide) hpro (by intro h; cases h)
    have hb' : (play q m).board = LoneKing.board .queen σ sk m.dst wk := by
      rw [hbp]; funext x; rw [hb, ht, esrc]; unfold LoneKing.board
      by_cases e1 : x = m.dst
      · subst e1; simp [hds]
      · by_cases e2 : x = rs
        · subst e2; simp [e1, Ne.symm h12, h23]
        · simp [e1, e2]
    have hfar : 2 ≤ dInf sk wk := by
      have h0 : dInf sk wk ≠ 0 := fun h => h13 (dInf_eq_zero_iff.1 h)
      have h1 : dInf sk wk ≠ 1 := by
        intro h
        have := (strong_check ⟨Ne.symm hds,h13,hdw,hb'⟩).2 (by rwa [dInf_comm])
        rw [this] at hc; cases hc
      omega
    exact Or.inr ⟨m.dst,⟨Ne.symm hds,h13,hdw,hb'⟩,
      by simp [play_turn,ht],hsee,hds,hdw,hfar⟩
  · rw [ht] at hcol
    exact False.elim (opp_ne _ hcol.symm)

end EndgameChess.Rules.KQK
