import EndgameChess.Rules.KPK.SupportedOutcome

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Prefix boards preceding the advance into the supported seventh-rank region. -/
def BelowSeventhPast (σ : Colour) (s : FreshGame.State) : Prop :=
  ∀ q ∈ s.past, ∃ a p b, IsKPK q σ a p b ∧ height σ p < 6

theorem below_past_count {s : FreshGame.State} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK s.board σ sk ps wk) (rank : height σ ps = 6)
    (past : BelowSeventhPast σ s) : FreshGame.occurrences s = 1 := by
  apply FreshGame.occurrences_one_of_key_ne
  intro q member
  obtain ⟨a, p, b, material, lower⟩ := past q member
  exact different_height_different_key material h (by omega)

theorem below_past_weak_count {s : FreshGame.State} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK s.board σ sk ps wk) (turn : s.board.turn = σ.opp)
    (support : SupportedSeventh σ sk ps) (past : BelowSeventhPast σ s)
    (legal : isLegal s.board m = true) :
    FreshGame.occurrences (FreshGame.afterMove s m) = 1 := by
  obtain ⟨t, material, nextTurn, _⟩ := supported_weak_reply h turn support ⟨m, legal, rfl⟩
  apply FreshGame.occurrences_one_of_key_ne
  intro q member same
  change q ∈ s.board :: s.past at member
  rcases List.mem_cons.mp member with current | old
  · subst q
    have turns : s.board.turn = (play s.board m).turn := by
      simpa only [RawRepetition.key, RawRepetition.normalizeEP, FreshGame.afterMove] using congrArg Position.turn same
    rw [turn, nextTurn] at turns
    exact opp_ne σ turns.symm
  · obtain ⟨a, p, b, oldMaterial, lower⟩ := past q old
    exact different_height_different_key oldMaterial material (by have := support.2.1; omega) same

/-- A pawn advance into the supported region may have an arbitrarily long
lower-height KPK prefix. The following weak turn still has no repetition claim. -/
theorem supported_weak_prefix_win {s : FreshGame.State} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK s.board σ sk ps wk) (turn : s.board.turn = σ.opp)
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk)
    (rights : s.board.castling = noRights) (past : BelowSeventhPast σ s)
    (zero : s.clock = 0) : FreshGame.Within σ 100 s := by
  have bound := supported_weak_bound h turn support far
  have moves := supported_weak_has_move h turn support far
  have count := below_past_count h support.2.1 past
  have ongoing : FreshGame.Ongoing s :=
    ⟨forceMate_not_dead ⟨100, bound⟩, moves, by omega, by omega⟩
  have all : ∀ u, FreshGame.BoardStep s u → FreshGame.Within σ 99 u := by
    intro u actual
    have legal := FreshGame.step_legal actual
    obtain ⟨t, material, nextTurn, apart⟩ := supported_weak_reply h turn support legal
    have nextBound := supported_strong_bound material nextTurn support apart
    obtain ⟨_, m, hm, rfl⟩ := actual
    have nextCount := below_past_weak_count h turn support past hm
    have nextClock := FreshGame.afterMove_clock_le s m
    have nextMoves : ∃ r, Legal (FreshGame.afterMove s m).board r := by
      have push := supported_promotion_push material support apart
      have last : (promotionSquare σ ps.1).2.val = lastRank σ := by cases σ <;> rfl
      exact ⟨_, _, promotion_legal material nextTurn apart push last .queen, rfl⟩
    have nextOngoing : FreshGame.Ongoing (FreshGame.afterMove s m) :=
      ⟨forceMate_not_dead ⟨99, nextBound⟩, nextMoves, by omega, by omega⟩
    apply supported_prefix_win material nextTurn support apart (noRights_after_legal rights legal)
      (ongoing := nextOngoing)
    intro q member
    change q ∈ s.board :: s.past at member
    rcases List.mem_cons.mp member with current | old
    · subst q; exact ⟨sk, ps, wk, h⟩
    · obtain ⟨a, p, b, hm, _⟩ := past q old
      exact ⟨a, p, b, hm⟩
  have noClaim : ¬ FreshGame.CanClaim s := by
    rintro (claim | ⟨m, legal, claim⟩)
    · rcases claim with clock | repetition <;> omega
    · have nextCount := below_past_weak_count h turn support past legal
      have nextClock := FreshGame.afterMove_clock_le s m
      rcases claim with clock | repetition <;> omega
  obtain ⟨r, legal⟩ := moves
  obtain ⟨u, actual, _⟩ := FreshGame.layer.reply_complete ongoing legal
  exact Or.inr ⟨ongoing, Or.inr ⟨turn, noClaim, ⟨u, actual⟩, all⟩⟩

end EndgameChess.Rules.KPK
