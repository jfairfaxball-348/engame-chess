import EndgameChess.Rules.KPK.Promotion

/-! Promotion continuation with the actual unpromoted prefix retained.
No arbitrary incoming-history classification is claimed. -/
namespace EndgameChess.Rules.KPK
open EndgameChess.KK

def HasPawn (q : Position) : Prop := ∃ s c, q.board s = some ⟨c, .pawn⟩

theorem material_has_pawn {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) : HasPawn q := by
  exact ⟨ps, σ, by rw [h.2.2.2]; exact LoneKing.board_xs h.1⟩

private def PromotedRegion (σ : Colour) (q : Position) : Prop :=
  (∃ k sk xs wk, k ≠ .king ∧ k ≠ .pawn ∧ LoneKing.Material k q σ sk xs wk ∧
    2 ≤ dInf sk wk ∧ q.castling = noRights) ∨ DeadK q

private theorem promoted_step {σ : Colour} {q r : Position}
    (region : PromotedRegion σ q) (legal : Legal q r) : PromotedRegion σ r := by
  rcases region with ⟨k, sk, xs, wk, nk, np, h, _, rights⟩ | dead
  · have nextRights := noRights_after_legal rights legal
    have enter {sk xs wk : Square} (hm : LoneKing.Material k r σ sk xs wk) : PromotedRegion σ r :=
      Or.inl ⟨k, sk, xs, wk, nk, np, hm,
        LoneKing.kings_apart_after nk hm legal, nextRights⟩
    rcases colour_cases σ q.turn with turn | turn
    · rcases LoneKing.strong_cases nk np h turn rights legal with ⟨t, hm⟩ | ⟨t, hm⟩
      · exact enter hm
      · exact enter hm
    · rcases LoneKing.weak_cases h turn legal with ⟨t, hm, _⟩ | ⟨w, b, kk⟩
      · exact enter hm
      · exact Or.inr (dead_of_legal_into_KK legal kk)
  · exact Or.inr (fun ⟨t, reach, mate⟩ => dead ⟨t, reachK_cons legal reach, mate⟩)

private theorem promoted_no_pawn {σ : Colour} {q : Position}
    (region : PromotedRegion σ q) (win : ForceMate σ q) : ¬ HasPawn q := by
  rcases region with ⟨k, sk, xs, wk, _, np, h, _⟩ | dead
  · rintro ⟨s, c, source⟩
    rw [h.2.2.2] at source
    rcases LoneKing.board_some source with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩
    · have kind := congrArg Piece.kind e; cases kind
    · exact np (congrArg Piece.kind e).symm
    · have kind := congrArg Piece.kind e; cases kind
  · exact False.elim (forceMate_not_dead win dead)

/-- Old pawn boards cannot repeat; newer promoted boards are ordered by strategy rank. -/
private def SeparatedPast (σ : Colour) (s : FreshGame.State) : Prop :=
  ∀ r ∈ s.past, HasPawn r ∨ strategyRank σ s.board < strategyRank σ r

private theorem one_occurrence {σ : Colour} {s : FreshGame.State}
    (region : PromotedRegion σ s.board) (win : ForceMate σ s.board)
    (history : SeparatedPast σ s) : FreshGame.occurrences s = 1 := by
  classical
  have empty : s.past.filter (fun q => decide (RawRepetition.key q = RawRepetition.key s.board)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q member hit
    have same := of_decide_eq_true hit
    rcases history q member with pawn | lower
    · have boards : q.board = s.board.board := by
        simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.board same
      apply promoted_no_pawn region win
      obtain ⟨t, c, source⟩ := pawn
      exact ⟨t, c, by rw [← boards]; exact source⟩
    · have ranks := strategy_rank_key (σ := σ) same
      omega
  simp only [FreshGame.occurrences, empty, List.length_nil, Nat.add_zero]

private theorem descend_past {σ : Colour} {s t : FreshGame.State}
    (history : SeparatedPast σ s) (actual : FreshGame.BoardStep s t)
    (policy : StrategyStep σ s.board t.board) : SeparatedPast σ t := by
  obtain ⟨_, m, _, rfl⟩ := actual
  intro r member
  change r ∈ s.board :: s.past at member
  rcases List.mem_cons.mp member with same | old
  · subst r; exact Or.inr policy.2.2.2
  · rcases history r old with pawn | rank
    · exact Or.inl pawn
    · exact Or.inr (Nat.lt_trans policy.2.2.2 rank)

private theorem lift_promoted (s : FreshGame.State) (σ : Colour) (n : Nat)
    (region : PromotedRegion σ s.board) (winning : MateWithin σ n s.board)
    (budget : s.clock + n < 100) (history : SeparatedPast σ s) : FreshGame.Within σ n s := by
  induction n generalizing s with
  | zero => exact winning
  | succ n ih =>
    by_cases goal : MateGoal σ s.board
    · exact Or.inl goal
    have win : ForceMate σ s.board := ⟨n+1, winning⟩
    have rankBound := (strategy_rank_spec win).2.1 (n+1) winning
    obtain ⟨strong, weak⟩ := strategy_progress win goal
    have moves : ∃ r, Legal s.board r := by
      rcases colour_cases σ s.board.turn with turn | turn
      · obtain ⟨r, step⟩ := strong turn; exact ⟨r, step.1⟩
      · exact (weak turn).1
    have count := one_occurrence region win history
    have ongoing : FreshGame.Ongoing s := ⟨forceMate_not_dead win, moves, by omega, by omega⟩
    have descend : ∀ t, FreshGame.BoardStep s t → StrategyStep σ s.board t.board →
        FreshGame.Within σ n t := by
      intro t actual policy
      have nextWin := policy.2.2.1
      have nextRank := policy.2.2.2
      have certificate : MateWithin σ n t.board :=
        mateWithin_mono (strategy_rank_spec nextWin).1 (by omega)
      have clock := FreshGame.clock_step_le actual
      exact ih t (promoted_step region (FreshGame.step_legal actual)) certificate
        (by omega) (descend_past history actual policy)
    refine Or.inr ⟨ongoing, ?_⟩
    rcases colour_cases σ s.board.turn with turn | turn
    · obtain ⟨r, policy⟩ := strong turn
      obtain ⟨t, actual, endpoint⟩ := FreshGame.layer.reply_complete ongoing policy.1
      change t.board = r at endpoint
      have next : StrategyStep σ s.board t.board := by rw [endpoint]; exact policy
      exact Or.inl ⟨turn, t, actual, descend t actual next⟩
    · have all := (weak turn).2
      have noClaim : ¬ FreshGame.CanClaim s := by
        rintro (current | ⟨m, hm, intended⟩)
        · rcases current with clock | repetition <;> omega
        · have actual : FreshGame.BoardStep s (FreshGame.afterMove s m) := ⟨ongoing, m, hm, rfl⟩
          have policy := all _ (show Legal s.board (FreshGame.afterMove s m).board from ⟨m, hm, rfl⟩)
          have nextCount := one_occurrence (promoted_step region policy.1) policy.2.2.1
            (descend_past history actual policy)
          have nextClock := FreshGame.clock_step_le actual
          rcases intended with clock | repetition <;> omega
      obtain ⟨r, hr⟩ := moves
      obtain ⟨t, actual, _⟩ := FreshGame.layer.reply_complete ongoing hr
      refine Or.inr ⟨turn, noClaim, ⟨t, actual⟩, ?_⟩
      intro t actual
      exact descend t actual (all _ (FreshGame.step_legal actual))

/-- Lift a proved promoted continuation after a KPK-only prefix. The original
past is retained, the pawn move really resets the clock, and every future
defending reply and draw claim is included. -/
theorem promotion_continuation {s : FreshGame.State} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK s.board σ sk ps wk) (ht : s.board.turn = σ)
    (far : 2 ≤ dInf sk wk) (rights : s.board.castling = noRights)
    (past : ∀ q ∈ s.past, ∃ a p b, IsKPK q σ a p b)
    (push : Push s.board σ ps t) (last : t.2.val = lastRank σ) (k : PromoPiece)
    {n : Nat} (bound : MateWithin σ n (play s.board (promote ps t k))) (small : n < 100) :
    FreshGame.Within σ n (FreshGame.afterMove s (promote ps t k)) := by
  have legal : Legal s.board (play s.board (promote ps t k)) :=
    ⟨_, promotion_legal h ht far push last k, rfl⟩
  have material := promotion_material h ht push k
  have nk : k.toKind ≠ .king := by cases k <;> decide
  have np : k.toKind ≠ .pawn := by cases k <;> decide
  have region : PromotedRegion σ (FreshGame.afterMove s (promote ps t k)).board :=
    Or.inl ⟨k.toKind, sk, t, wk, nk, np, material,
      LoneKing.kings_apart_after nk material legal, noRights_after_legal rights legal⟩
  apply lift_promoted _ σ n region bound
  · rw [pawn_resets_clock h ht rfl]; simpa only [Nat.zero_add] using small
  · intro q member
    change q ∈ s.board :: s.past at member
    left
    rcases List.mem_cons.mp member with same | old
    · subst q; exact material_has_pawn h
    · obtain ⟨a, p, b, hm⟩ := past q old
      exact material_has_pawn hm

/-- Every winning queen promotion has a 98-ply continuation with its KPK prefix retained. -/
theorem queen_prefix_continuation {s : FreshGame.State} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK s.board σ sk ps wk) (ht : s.board.turn = σ)
    (far : 2 ≤ dInf sk wk) (rights : s.board.castling = noRights)
    (past : ∀ q ∈ s.past, ∃ a p b, IsKPK q σ a p b)
    (push : Push s.board σ ps t) (last : t.2.val = lastRank σ)
    (win : ForceMate σ (play s.board (promote ps t .queen))) :
    FreshGame.Within σ 98 (FreshGame.afterMove s (promote ps t .queen)) := by
  have material := promotion_material h ht push .queen
  have turn : (play s.board (promote ps t .queen)).turn = σ.opp := by rw [play_turn, ht]
  have bound : MateWithin σ 98 (play s.board (promote ps t .queen)) := by
    rcases (KQK.weak_force_safe_iff material turn).mp win with mate | ⟨safe, moves⟩
    · exact mateWithin_mono (show MateWithin σ 0 _ from ⟨turn, mate⟩) (by decide)
    · exact KQK.safe_weak_entry_bound material turn safe moves
  exact promotion_continuation h ht far rights past push last .queen bound (by decide)

theorem rook_prefix_continuation {s : FreshGame.State} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK s.board σ sk ps wk) (ht : s.board.turn = σ)
    (far : 2 ≤ dInf sk wk) (rights : s.board.castling = noRights)
    (past : ∀ q ∈ s.past, ∃ a p b, IsKPK q σ a p b)
    (push : Push s.board σ ps t) (last : t.2.val = lastRank σ)
    (win : ForceMate σ (play s.board (promote ps t .rook))) :
    FreshGame.Within σ 98 (FreshGame.afterMove s (promote ps t .rook)) := by
  have material := promotion_material h ht push .rook
  have turn : (play s.board (promote ps t .rook)).turn = σ.opp := by rw [play_turn, ht]
  exact promotion_continuation h ht far rights past push last .rook
    (KRKCentral.weak98 material turn win) (by decide)

end EndgameChess.Rules.KPK
