import EndgameChess.Rules.KRKTermination.Castle
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Every legal strong move preserves exact KRK, including actual castling. -/
theorem krk_strong_material {q : Position} {σ : Colour} {sk rs wk : Square} {m : Move}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (hm : isLegal q m = true) :
    ∃ ns nr, IsKRK (play q m) σ ns nr wk := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have hp : isPseudo q m = true := by
    unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  obtain ⟨pc, hpc, hcol⟩ := own_of_isPseudo hp
  rw [hb] at hpc
  rcases krkBoard_some hpc with ⟨esrc, rfl⟩ | ⟨esrc, rfl⟩ | ⟨_, rfl⟩
  · have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by rw [hb, ht, esrc]; exact krkBoard_sk
    rw [isPseudo_of_king hsrc] at hp
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true] at hp
    obtain ⟨htg, hpro, hg⟩ := hp
    by_cases castle : canCastle q m = true
    · exact krk_castle_material ⟨h12, h13, h23, hb⟩ ht esrc castle
    have hg := hg.resolve_right castle
    have hd : dInf sk m.dst = 1 := by rw [← esrc]; exact kingGeom_iff.1 hg
    have hds : m.dst ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
    have hdr : m.dst ≠ rs := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact krkBoard_rs h12)).1
      exact this (by rw [ht])
    have hdw : m.dst ≠ wk := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact krkBoard_wk h13 h23)).2
      exact this rfl
    have hbp := play_board_simple hsrc (by decide) hpro (fun _ => by rw [esrc]; exact hd)
    have hb' : (play q m).board = krkBoard σ m.dst rs wk := by
      rw [hbp]; funext x; rw [hb, ht, esrc]; unfold krkBoard
      by_cases e1 : x = m.dst
      · subst e1; simp
      · by_cases e2 : x = sk
        · subst e2; simp [e1, h12, h13]
        · simp [e1, e2]
    exact ⟨m.dst, rs, hdr, hdw, h23, hb'⟩
  · have hsrc : q.board m.src = some ⟨q.turn, .rook⟩ := by rw [hb, ht, esrc]; exact krkBoard_rs h12
    have hp' := hp
    unfold isPseudo at hp'
    rw [hsrc] at hp'
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at hp'
    obtain ⟨htg, hpro, hatt⟩ := hp'
    have hsee : RookSees rs m.dst sk wk := by
      rw [hb, ht, esrc] at hatt
      exact (rook_attacks_krk h12 _).1 hatt
    have hds : m.dst ≠ sk := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact krkBoard_sk)).2
      exact this rfl
    have hdr : m.dst ≠ rs := ne_of_rookLine hsee.1
    have hdw : m.dst ≠ wk := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact krkBoard_wk h13 h23)).2
      exact this rfl
    have hbp := play_board_simple hsrc (by decide) hpro (by intro h; cases h)
    have hb' : (play q m).board = krkBoard σ sk m.dst wk := by
      rw [hbp]; funext x; rw [hb, ht, esrc]; unfold krkBoard
      by_cases e1 : x = m.dst
      · subst e1; simp [hds]
      · by_cases e2 : x = rs
        · subst e2; simp [e1, Ne.symm h12, h23]
        · simp [e1, e2]
    exact ⟨sk, m.dst, Ne.symm hds, h13, hdw, hb'⟩
  · rw [ht] at hcol
    exact False.elim (opp_ne _ hcol.symm)

end EndgameChess.Rules
