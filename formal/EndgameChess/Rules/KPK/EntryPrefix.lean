import EndgameChess.Rules.KPK.SeventhKingOutcome

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

theorem seventh_king_weak_board_bound {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk)
    (notCorner : ¬ SixthCornerStalemate σ ps wk) : MateWithin σ 102 q := by
  have moves := (seventh_king_moves_iff h turn band far).mpr notCorner
  have all : ∀ r, Legal q r → MateWithin σ 101 r := by
    intro r legal
    obtain ⟨t, material, nextTurn, apart⟩ := seventh_king_weak_reply h turn band legal
    exact seventh_king_strong_bound material nextTurn band apart
  have live : ¬ DeadK q := by
    obtain ⟨r, legal⟩ := moves
    obtain ⟨t, reach, goal⟩ := mateWithin_sound (all r legal)
    exact fun dead => dead ⟨t, reachK_cons legal reach, goal.2⟩
  exact Or.inr ⟨live, Or.inr ⟨turn, moves, all⟩⟩

/-- A quiet king entry into the supported seventh-rank band retains its
one-board prefix; the next promotion supplies the actual reset. -/
theorem supported_weak_one_ply {s : FreshGame.State} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK s.board σ sk ps wk) (turn : s.board.turn = σ.opp)
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk)
    (rights : s.board.castling = noRights)
    (past : ∀ q ∈ s.past, ∃ a p b, IsKPK q σ a p b)
    (clock : s.clock ≤ 1) (length : s.past.length ≤ 1) : FreshGame.Within σ 100 s := by
  have boardBound := supported_weak_bound h turn support far
  have moves := supported_weak_has_move h turn support far
  have count := FreshGame.occurrences_le_past s
  have ongoing : FreshGame.Ongoing s :=
    ⟨forceMate_not_dead ⟨100, boardBound⟩, moves, by omega, by omega⟩
  have all : ∀ u, FreshGame.BoardStep s u → FreshGame.Within σ 99 u := by
    intro u actual
    have legal := FreshGame.step_legal actual
    obtain ⟨t, material, nextTurn, apart⟩ := supported_weak_reply h turn support legal
    have bound := supported_strong_bound material nextTurn support apart
    obtain ⟨_, m, hm, rfl⟩ := actual
    have nextClock := FreshGame.afterMove_clock_le s m
    have nextCount := FreshGame.occurrences_le_past (FreshGame.afterMove s m)
    have nextLength : (FreshGame.afterMove s m).past.length ≤ 2 := by
      change s.past.length + 1 ≤ 2
      omega
    have nextMoves : ∃ r, Legal (FreshGame.afterMove s m).board r := by
      have push := supported_promotion_push material support apart
      have last : (promotionSquare σ ps.1).2.val = lastRank σ := by cases σ <;> rfl
      exact ⟨_, _, promotion_legal material nextTurn apart push last .queen, rfl⟩
    have nextOngoing : FreshGame.Ongoing (FreshGame.afterMove s m) :=
      ⟨forceMate_not_dead ⟨99, bound⟩, nextMoves, by omega, by omega⟩
    apply supported_prefix_win material nextTurn support apart (noRights_after_legal rights legal)
      (ongoing := nextOngoing)
    intro q member
    change q ∈ s.board :: s.past at member
    rcases List.mem_cons.mp member with current | old
    · subst q; exact ⟨sk, ps, wk, h⟩
    · exact past q old
  obtain ⟨r, legal⟩ := moves
  obtain ⟨u, actual, _⟩ := FreshGame.layer.reply_complete ongoing legal
  exact Or.inr ⟨ongoing, Or.inr ⟨turn, FreshGame.one_ply_no_claim clock length, ⟨u, actual⟩, all⟩⟩

/-- One quiet king move before the sixth-pawn band also permits the next
pawn advance: older boards are below height six and become nonrepeating. -/
theorem seventh_king_weak_one_ply {s : FreshGame.State} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK s.board σ sk ps wk) (turn : s.board.turn = σ.opp)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk)
    (notCorner : ¬ SixthCornerStalemate σ ps wk)
    (rights : s.board.castling = noRights) (past : BelowSeventhPast σ s)
    (clock : s.clock ≤ 1) (length : s.past.length ≤ 1) : FreshGame.Within σ 102 s := by
  have boardBound := seventh_king_weak_board_bound h turn band far notCorner
  have moves := (seventh_king_moves_iff h turn band far).mpr notCorner
  have count := FreshGame.occurrences_le_past s
  have ongoing : FreshGame.Ongoing s :=
    ⟨forceMate_not_dead ⟨102, boardBound⟩, moves, by omega, by omega⟩
  have all : ∀ u, FreshGame.BoardStep s u → FreshGame.Within σ 101 u := by
    intro u actual
    have legal := FreshGame.step_legal actual
    obtain ⟨t, material, nextTurn, apart⟩ := seventh_king_weak_reply h turn band legal
    have bound := seventh_king_strong_bound material nextTurn band apart
    obtain ⟨_, m, hm, rfl⟩ := actual
    have nextClock := FreshGame.afterMove_clock_le s m
    have nextCount := FreshGame.occurrences_le_past (FreshGame.afterMove s m)
    have nextLength : (FreshGame.afterMove s m).past.length ≤ 2 := by
      change s.past.length + 1 ≤ 2
      omega
    have nextMoves : ∃ r, Legal (FreshGame.afterMove s m).board r :=
      ⟨_, _, seventh_king_advance_legal material nextTurn band apart, rfl⟩
    have nextOngoing : FreshGame.Ongoing (FreshGame.afterMove s m) :=
      ⟨forceMate_not_dead ⟨101, bound⟩, nextMoves, by omega, by omega⟩
    apply seventh_king_strong_prefix material nextTurn band apart (noRights_after_legal rights legal)
      (ongoing := nextOngoing)
    intro q member
    change q ∈ s.board :: s.past at member
    rcases List.mem_cons.mp member with current | old
    · subst q; exact ⟨sk, ps, wk, h, by have := band.2.1; omega⟩
    · exact past q old
  obtain ⟨r, legal⟩ := moves
  obtain ⟨u, actual, _⟩ := FreshGame.layer.reply_complete ongoing legal
  exact Or.inr ⟨ongoing, Or.inr ⟨turn, FreshGame.one_ply_no_claim clock length, ⟨u, actual⟩, all⟩⟩

/-- A two-quiet-ply entry is also admissible when its actual prefix has
no claim. The next strong move advances the pawn and separates old heights. -/
theorem seventh_king_weak_two_ply {s : FreshGame.State} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK s.board σ sk ps wk) (turn : s.board.turn = σ.opp)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk)
    (notCorner : ¬ SixthCornerStalemate σ ps wk)
    (rights : s.board.castling = noRights) (past : BelowSeventhPast σ s)
    (clock : s.clock ≤ 2) (length : s.past.length ≤ 2)
    (noClaim : ¬ FreshGame.CanClaim s) : FreshGame.Within σ 102 s := by
  have boardBound := seventh_king_weak_board_bound h turn band far notCorner
  have moves := (seventh_king_moves_iff h turn band far).mpr notCorner
  have count := FreshGame.occurrences_le_past s
  have ongoing : FreshGame.Ongoing s :=
    ⟨forceMate_not_dead ⟨102, boardBound⟩, moves, by omega, by omega⟩
  have all : ∀ u, FreshGame.BoardStep s u → FreshGame.Within σ 101 u := by
    intro u actual
    have legal := FreshGame.step_legal actual
    obtain ⟨t, material, nextTurn, apart⟩ := seventh_king_weak_reply h turn band legal
    have bound := seventh_king_strong_bound material nextTurn band apart
    obtain ⟨_, m, hm, rfl⟩ := actual
    have nextClock := FreshGame.afterMove_clock_le s m
    have nextCount := FreshGame.occurrences_le_past (FreshGame.afterMove s m)
    have nextLength : (FreshGame.afterMove s m).past.length ≤ 3 := by
      change s.past.length + 1 ≤ 3
      omega
    have nextMoves : ∃ r, Legal (FreshGame.afterMove s m).board r :=
      ⟨_, _, seventh_king_advance_legal material nextTurn band apart, rfl⟩
    have nextOngoing : FreshGame.Ongoing (FreshGame.afterMove s m) :=
      ⟨forceMate_not_dead ⟨101, bound⟩, nextMoves, by omega, by omega⟩
    apply seventh_king_strong_prefix material nextTurn band apart (noRights_after_legal rights legal)
      (ongoing := nextOngoing)
    intro q member
    change q ∈ s.board :: s.past at member
    rcases List.mem_cons.mp member with current | old
    · subst q; exact ⟨sk, ps, wk, h, by have := band.2.1; omega⟩
    · exact past q old
  obtain ⟨r, legal⟩ := moves
  obtain ⟨u, actual, _⟩ := FreshGame.layer.reply_complete ongoing legal
  exact Or.inr ⟨ongoing, Or.inr ⟨turn, noClaim, ⟨u, actual⟩, all⟩⟩

end EndgameChess.Rules.KPK
