import EndgameChess.Rules.FreshGame.Definitions

namespace EndgameChess.Rules.FreshGame
open EndgameChess.KK

private def DescendingPast (σ : Colour) (s : State) : Prop :=
  ∀ r ∈ s.past, strategyRank σ s.board < strategyRank σ r

private theorem one_occurrence {σ : Colour} {s : State} (history : DescendingPast σ s) :
    occurrences s = 1 := by
  classical
  have empty : s.past.filter (fun q => decide (RawRepetition.key q = RawRepetition.key s.board)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q member hit
    have same := strategy_rank_key (σ := σ) (of_decide_eq_true hit)
    have smaller := history q member
    omega
  simp only [occurrences,empty,List.length_nil,Nat.add_zero]

private theorem descend_past {σ : Colour} {s t : State} (history : DescendingPast σ s)
    (actual : BoardStep s t) (policy : StrategyStep σ s.board t.board) : DescendingPast σ t := by
  obtain ⟨_,m,_,rfl⟩ := actual
  intro r member
  change r ∈ s.board::s.past at member
  rcases List.mem_cons.mp member with same | old
  · subst r; exact policy.2.2.2
  · exact Nat.lt_trans policy.2.2.2 (history r old)

private theorem lift (s : State) (σ : Colour) (n : Nat)
    (winning : MateWithin σ n s.board) (budget : s.clock+n < 100)
    (history : DescendingPast σ s) : Within σ n s := by
  induction n generalizing s with
  | zero => exact winning
  | succ n ih =>
    by_cases goal : MateGoal σ s.board
    · exact Or.inl goal
    have win : ForceMate σ s.board := ⟨n+1,winning⟩
    have rankBound := (strategy_rank_spec win).2.1 (n+1) winning
    obtain ⟨strong,weak⟩ := strategy_progress win goal
    have moves : ∃ r, Legal s.board r := by
      rcases colour_cases σ s.board.turn with turn | turn
      · obtain ⟨r,step⟩ := strong turn; exact ⟨r,step.1⟩
      · exact (weak turn).1
    have count := one_occurrence history
    have ongoing : Ongoing s := ⟨forceMate_not_dead win,moves,by omega,by omega⟩
    have descend : ∀ t, BoardStep s t → StrategyStep σ s.board t.board → Within σ n t := by
      intro t actual policy
      have nextWin := policy.2.2.1
      have nextRank := policy.2.2.2
      have certificate : MateWithin σ n t.board :=
        mateWithin_mono (strategy_rank_spec nextWin).1 (by omega)
      have clock := clock_step_le actual
      exact ih t certificate (by omega) (descend_past history actual policy)
    refine Or.inr ⟨ongoing,?_⟩
    rcases colour_cases σ s.board.turn with turn | turn
    · obtain ⟨r,policy⟩ := strong turn
      obtain ⟨t,actual,endpoint⟩ := layer.reply_complete ongoing policy.1
      change t.board = r at endpoint
      have next : StrategyStep σ s.board t.board := by rw [endpoint]; exact policy
      exact Or.inl ⟨turn,t,actual,descend t actual next⟩
    · have all := (weak turn).2
      have noClaim : ¬ CanClaim s := by
        rintro (current | ⟨m,hm,intended⟩)
        · rcases current with clock | repetition <;> omega
        · have actual : BoardStep s (afterMove s m) := ⟨ongoing,m,hm,rfl⟩
          have policy := all _ (show Legal s.board (afterMove s m).board from ⟨m,hm,rfl⟩)
          have nextCount := one_occurrence (descend_past history actual policy)
          have nextClock := clock_step_le actual
          rcases intended with clock | repetition <;> omega
      obtain ⟨r,hr⟩ := moves
      obtain ⟨t,actual,_⟩ := layer.reply_complete ongoing hr
      refine Or.inr ⟨turn,noClaim,⟨t,actual⟩,?_⟩
      intro t actual
      exact descend t actual (all _ (step_legal actual))

/-- A fresh, history-free root lifts every supplied sub100 board bound.
The chosen decreasing strategy rank prevents all future key repetitions;
captures and pawn moves use the kernel's actual clock reset. -/
theorem fresh_sub100 {q : Position} {σ : Colour} {n : Nat}
    (winning : MateWithin σ n q) (small : n < 100) : Within σ n (fresh q) := by
  apply lift (fresh q) σ n winning (by simpa only [fresh,Nat.zero_add] using small)
  intro r member
  exact False.elim (List.not_mem_nil member)

theorem win_project {s : State} {σ : Colour} (win : Win σ s) : ForceMate σ s.board := by
  obtain ⟨n,certificate⟩ := win
  exact ⟨n,HistoryLayer.ruleMateWithin_project layer certificate⟩

end EndgameChess.Rules.FreshGame
