import EndgameChess.Rules.KPK.SeventhKing

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

theorem seventh_king_strong_bound {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk) : MateWithin σ 101 q := by
  obtain ⟨push, support⟩ := seventh_king_advance h band far
  let m : Move := ⟨ps, atHeight σ ps.1 6, none⟩
  have hm := seventh_king_advance_legal h turn band far
  have legal : Legal q (play q m) := ⟨m, hm, rfl⟩
  have material : IsKPK (play q m) σ sk (atHeight σ ps.1 6) wk :=
    pawn_play_material h turn (m := m) rfl push
  have nextTurn : (play q m).turn = σ.opp := by rw [play_turn, turn]
  exact choose_bound turn legal (supported_weak_bound material nextTurn support far)

/-- The advance resets the clock before the 100-ply supported continuation. -/
theorem seventh_king_strong_prefix {s : FreshGame.State} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK s.board σ sk ps wk) (turn : s.board.turn = σ)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk)
    (rights : s.board.castling = noRights) (past : BelowSeventhPast σ s)
    (ongoing : FreshGame.Ongoing s) : FreshGame.Within σ 101 s := by
  obtain ⟨push, support⟩ := seventh_king_advance h band far
  let m : Move := ⟨ps, atHeight σ ps.1 6, none⟩
  have hm := seventh_king_advance_legal h turn band far
  have legal : Legal s.board (play s.board m) := ⟨m, hm, rfl⟩
  have material : IsKPK (play s.board m) σ sk (atHeight σ ps.1 6) wk :=
    pawn_play_material h turn (m := m) rfl push
  have nextTurn : (play s.board m).turn = σ.opp := by rw [play_turn, turn]
  have nextPast : BelowSeventhPast σ (FreshGame.afterMove s m) := by
    intro q member
    change q ∈ s.board :: s.past at member
    rcases List.mem_cons.mp member with current | old
    · subst q; exact ⟨sk, ps, wk, h, by have := band.2.1; omega⟩
    · exact past q old
  have continuation : FreshGame.Within σ 100 (FreshGame.afterMove s m) :=
    supported_weak_prefix_win material nextTurn support far
      (noRights_after_legal rights legal) nextPast (pawn_resets_clock h turn rfl)
  exact Or.inr ⟨ongoing, Or.inl ⟨turn, FreshGame.afterMove s m,
    ⟨ongoing, m, hm, rfl⟩, continuation⟩⟩

theorem fresh_seventh_king_strong {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (band : SeventhKing σ sk ps) : FreshGame.Within σ 101 (FreshGame.fresh q) := by
  have bound := seventh_king_strong_bound h turn band fresh.kings
  have moves : ∃ r, Legal q r :=
    ⟨_, _, seventh_king_advance_legal h turn band fresh.kings, rfl⟩
  have count := FreshGame.occurrences_le_past (FreshGame.fresh q)
  have ongoing : FreshGame.Ongoing (FreshGame.fresh q) := by
    refine ⟨forceMate_not_dead ⟨101, bound⟩, moves, ?_, ?_⟩
    · change 0 < 150; decide
    · change FreshGame.occurrences (FreshGame.fresh q) ≤ 0 + 1 at count; omega
  apply seventh_king_strong_prefix h turn band fresh.kings fresh.rights (ongoing := ongoing)
  intro r member
  exact False.elim (List.not_mem_nil member)

theorem fresh_seventh_king_weak {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (band : SeventhKing σ sk ps) (notCorner : ¬ SixthCornerStalemate σ ps wk) :
    FreshGame.Within σ 102 (FreshGame.fresh q) := by
  have moves := (seventh_king_moves_iff h turn band fresh.kings).mpr notCorner
  have allBoard : ∀ r, Legal q r → MateWithin σ 101 r := by
    intro r legal
    obtain ⟨t, material, nextTurn, apart⟩ := seventh_king_weak_reply h turn band legal
    exact seventh_king_strong_bound material nextTurn band apart
  have live : ¬ DeadK q := by
    obtain ⟨r, legal⟩ := moves
    obtain ⟨t, reach, goal⟩ := mateWithin_sound (allBoard r legal)
    exact fun dead => dead ⟨t, reachK_cons legal reach, goal.2⟩
  have count := FreshGame.occurrences_le_past (FreshGame.fresh q)
  have ongoing : FreshGame.Ongoing (FreshGame.fresh q) := by
    refine ⟨live, moves, ?_, ?_⟩
    · change 0 < 150; decide
    · change FreshGame.occurrences (FreshGame.fresh q) ≤ 0 + 1 at count; omega
  have all : ∀ s, FreshGame.BoardStep (FreshGame.fresh q) s → FreshGame.Within σ 101 s := by
    intro s actual
    have legal := FreshGame.step_legal actual
    obtain ⟨t, material, nextTurn, apart⟩ := seventh_king_weak_reply h turn band legal
    have nextBound := seventh_king_strong_bound material nextTurn band apart
    obtain ⟨_, m, hm, rfl⟩ := actual
    have nextClock := FreshGame.afterMove_clock_le (FreshGame.fresh q) m
    have nextCount := FreshGame.occurrences_le_past (FreshGame.afterMove (FreshGame.fresh q) m)
    have nextMoves : ∃ r, Legal (FreshGame.afterMove (FreshGame.fresh q) m).board r :=
      ⟨_, _, seventh_king_advance_legal material nextTurn band apart, rfl⟩
    have nextOngoing : FreshGame.Ongoing (FreshGame.afterMove (FreshGame.fresh q) m) := by
      refine ⟨forceMate_not_dead ⟨101, nextBound⟩, nextMoves, ?_, ?_⟩
      · change (FreshGame.afterMove (FreshGame.fresh q) m).clock ≤ 0 + 1 at nextClock; omega
      · change FreshGame.occurrences (FreshGame.afterMove (FreshGame.fresh q) m) ≤ 1 + 1 at nextCount; omega
    apply seventh_king_strong_prefix material nextTurn band apart
      (noRights_after_legal fresh.rights legal) (ongoing := nextOngoing)
    intro r member
    change r ∈ [q] at member
    have same : r = q := List.mem_singleton.mp member
    subst r
    exact ⟨sk, ps, wk, h, by have := band.2.1; omega⟩
  obtain ⟨r, legal⟩ := moves
  obtain ⟨s, actual, _⟩ := FreshGame.layer.reply_complete ongoing legal
  exact Or.inr ⟨ongoing, Or.inr ⟨turn, FreshGame.fresh_no_claim q, ⟨s, actual⟩, all⟩⟩

/-- Closed coordinate/turn criterion for this whole king/pawn band. -/
def SeventhKingWins (σ : Colour) (q : Position) (ps wk : Square) : Prop :=
  q.turn = σ ∨ ¬ SixthCornerStalemate σ ps wk

theorem seventh_king_losing_dead {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk)
    (band : SeventhKing σ sk ps) (losing : ¬ SeventhKingWins σ q ps wk) : DeadK q := by
  have turn : q.turn = σ.opp := by
    rcases colour_cases σ q.turn with strong | weak
    · exact False.elim (losing (Or.inl strong))
    · exact weak
  have corner : SixthCornerStalemate σ ps wk := Classical.byContradiction
    (fun notCorner => losing (Or.inr notCorner))
  have noMoves := sixth_corner_no_moves h turn band fresh.kings corner
  exact dead_of_succ_KK (not_mated h fresh.kings) (fun r legal => False.elim (noMoves ⟨r, legal⟩))

/-- Complete WDL50 and dead/live for this explicitly stated band only.
The 101/102 total allows pawn resets; it is not a quiet-move bound. -/
theorem fresh_seventh_king_wdl50 {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (band : SeventhKing σ sk ps) :
    (FreshGame.ActualWin σ (FreshGame.fresh q) ↔ SeventhKingWins σ q ps wk) ∧
    ¬ FreshGame.ActualWin σ.opp (FreshGame.fresh q) ∧
    ((FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q)) ↔
      ¬ SeventhKingWins σ q ps wk) ∧
    (DeadK q ↔ ¬ SeventhKingWins σ q ps wk) := by
  have winning : SeventhKingWins σ q ps wk → FreshGame.ActualWin σ (FreshGame.fresh q) := by
    intro criterion
    apply FreshGame.actual_win_of_rule
    rcases colour_cases σ q.turn with turn | turn
    · exact ⟨101, fresh_seventh_king_strong h fresh turn band⟩
    · have notCorner : ¬ SixthCornerStalemate σ ps wk := by
        rcases criterion with wrong | notCorner
        · exact False.elim (opp_ne σ (wrong.symm.trans turn))
        · exact notCorner
      exact ⟨102, fresh_seventh_king_weak h fresh turn band notCorner⟩
  have draw : ¬ SeventhKingWins σ q ps wk →
      FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q) := by
    intro losing
    have dead := seventh_king_losing_dead h fresh band losing
    refine ⟨fresh_strong_hold h fresh, FreshGame.terminal_hold (fun ongoing => ongoing.1 dead) ?_⟩
    exact fun goal => not_mated h fresh.kings goal.2
  have converse : FreshGame.ActualWin σ (FreshGame.fresh q) → SeventhKingWins σ q ps wk := by
    intro win
    apply Classical.byContradiction
    intro losing
    have noWin := FreshGame.hold_not_win (draw losing).2
    rw [opp_opp] at noWin
    exact noWin (FreshGame.actual_win_iff_rule.mp win)
  refine ⟨⟨converse, winning⟩, fresh_no_weak_actual_win h fresh, ⟨?_, draw⟩, ?_⟩
  · rintro ⟨_, hold⟩ criterion
    have noWin := FreshGame.hold_not_win hold
    rw [opp_opp] at noWin
    exact noWin (FreshGame.actual_win_iff_rule.mp (winning criterion))
  · constructor
    · intro dead criterion
      exact forceMate_not_dead (FreshGame.win_project (FreshGame.actual_win_iff_rule.mp (winning criterion))) dead
    · exact seventh_king_losing_dead h fresh band

/-- In this band every no-limit win also wins under the fresh 50-move rule.
Thus no cursed-win/blessed-loss exception occurs within the stated domain. -/
theorem seventh_king_force_iff_fresh {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (band : SeventhKing σ sk ps) :
    ForceMate σ q ↔ FreshGame.ActualWin σ (FreshGame.fresh q) := by
  constructor
  · intro force
    apply (fresh_seventh_king_wdl50 h fresh band).1.mpr
    apply Classical.byContradiction
    intro losing
    exact forceMate_not_dead force (seventh_king_losing_dead h fresh band losing)
  · intro actual
    exact FreshGame.win_project (FreshGame.actual_win_iff_rule.mp actual)

end EndgameChess.Rules.KPK
