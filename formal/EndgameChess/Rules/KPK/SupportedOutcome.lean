import EndgameChess.Rules.KPK.SupportedPromotion
import EndgameChess.Rules.FreshGame.ShortPrefix

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Promotion from an ongoing KPK-only prefix, retaining its history and actual reset. -/
theorem supported_prefix_win {s : FreshGame.State} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK s.board σ sk ps wk) (turn : s.board.turn = σ)
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk)
    (rights : s.board.castling = noRights)
    (past : ∀ q ∈ s.past, ∃ a p b, IsKPK q σ a p b)
    (ongoing : FreshGame.Ongoing s) : FreshGame.Within σ 99 s := by
  let m := promote ps (promotionSquare σ ps.1) .queen
  have push := supported_promotion_push h support far
  have last : (promotionSquare σ ps.1).2.val = lastRank σ := by cases σ <;> rfl
  have legal : isLegal s.board m = true := promotion_legal h turn far push last .queen
  have continuation : FreshGame.Within σ 98 (FreshGame.afterMove s m) :=
    promotion_continuation h turn far rights past push last .queen
      (supported_queen_successor_bound h turn support far) (by decide)
  exact Or.inr ⟨ongoing, Or.inl ⟨turn, FreshGame.afterMove s m,
    ⟨ongoing, m, legal, rfl⟩, continuation⟩⟩

/-- The weak-turn 100-ply total uses a real pawn reset after the first reply. -/
theorem fresh_supported_weak {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (support : SupportedSeventh σ sk ps) : FreshGame.Within σ 100 (FreshGame.fresh q) := by
  have boardBound := supported_weak_bound h turn support fresh.kings
  have moves := supported_weak_has_move h turn support fresh.kings
  have count := FreshGame.occurrences_le_past (FreshGame.fresh q)
  have ongoing : FreshGame.Ongoing (FreshGame.fresh q) :=
    ⟨forceMate_not_dead ⟨100, boardBound⟩, moves, by change 0 < 150; decide, by
      change FreshGame.occurrences (FreshGame.fresh q) ≤ 0 + 1 at count
      omega⟩
  have all : ∀ s, FreshGame.BoardStep (FreshGame.fresh q) s → FreshGame.Within σ 99 s := by
    intro s actual
    have legal := FreshGame.step_legal actual
    obtain ⟨t, material, nextTurn, apart⟩ := supported_weak_reply h turn support legal
    have bound := supported_strong_bound material nextTurn support apart
    obtain ⟨_, m, hm, rfl⟩ := actual
    have past : ∀ r ∈ (FreshGame.afterMove (FreshGame.fresh q) m).past,
        ∃ a p b, IsKPK r σ a p b := by
      intro r member
      change r ∈ [q] at member
      have same : r = q := List.mem_singleton.mp member
      subst r; exact ⟨sk, ps, wk, h⟩
    have rights := noRights_after_legal fresh.rights legal
    have nextMoves : ∃ r, Legal (FreshGame.afterMove (FreshGame.fresh q) m).board r := by
      have push := supported_promotion_push material support apart
      have last : (promotionSquare σ ps.1).2.val = lastRank σ := by cases σ <;> rfl
      exact ⟨_, _, promotion_legal material nextTurn apart push last .queen, rfl⟩
    have nextClock := FreshGame.afterMove_clock_le (FreshGame.fresh q) m
    have nextCount := FreshGame.occurrences_le_past (FreshGame.afterMove (FreshGame.fresh q) m)
    have nextOngoing : FreshGame.Ongoing (FreshGame.afterMove (FreshGame.fresh q) m) := by
      refine ⟨forceMate_not_dead ⟨99, bound⟩, nextMoves, ?_, ?_⟩
      · change (FreshGame.afterMove (FreshGame.fresh q) m).clock ≤ 0 + 1 at nextClock
        omega
      · change FreshGame.occurrences (FreshGame.afterMove (FreshGame.fresh q) m) ≤ 1 + 1 at nextCount
        omega
    exact supported_prefix_win material nextTurn support apart rights past nextOngoing
  obtain ⟨r, legal⟩ := moves
  obtain ⟨s, actual, _⟩ := FreshGame.layer.reply_complete ongoing legal
  exact Or.inr ⟨ongoing, Or.inr ⟨turn, FreshGame.fresh_no_claim q, ⟨s, actual⟩, all⟩⟩

/-- Both-colour, both-turn actual winning region, with sufficient (not optimal) bounds. -/
theorem fresh_supported_win {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk)
    (support : SupportedSeventh σ sk ps) : FreshGame.ActualWin σ (FreshGame.fresh q) := by
  apply FreshGame.actual_win_of_rule
  rcases colour_cases σ q.turn with turn | turn
  · exact ⟨99, fresh_supported_strong h fresh turn support⟩
  · exact ⟨100, fresh_supported_weak h fresh turn support⟩

end EndgameChess.Rules.KPK
