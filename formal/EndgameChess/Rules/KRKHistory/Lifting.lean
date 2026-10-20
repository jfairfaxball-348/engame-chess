import EndgameChess.Rules.KRKHistory.Append
namespace EndgameChess.Rules.RawHistoryLayer
open EndgameChess.KK

/-- Same supplied budget under strategy-specific static incoming-history conditions. -/
theorem raw_ruleMateWithin_of_strategy_history (s : State) (σ : Colour) (n : Nat)
    (winning : MateWithin σ n (erase s))
    (clockBudget : RawClock.clock s.val.trace + n < 100)
    (rootCount : RawRepetition.currentOccurrences s.val < 3)
    (hist : LowerRankHistory σ s.val) :
    HistoryLayer.RuleMateWithin layer σ n s := by
  induction n generalizing s with
  | zero => exact winning
  | succ n ih =>
    by_cases goal : MateGoal σ (erase s)
    · exact Or.inl goal
    have win : ForceMate σ (erase s) := ⟨n + 1, winning⟩
    have rankBound := (strategy_rank_spec win).2.1 (n + 1) winning
    obtain ⟨strong, weak⟩ := strategy_progress win goal
    have moves : ∃ r, Legal (erase s) r := by
      by_cases turn : (erase s).turn = σ
      · obtain ⟨r, step⟩ := strong turn
        exact ⟨r, step.1⟩
      · have other : (erase s).turn = σ.opp := by
          cases σ <;> cases h : (erase s).turn <;> simp_all [Colour.opp]
        exact (weak other).1
    have ongoing : Ongoing s := (RawAdjudication.ongoing_iff s.val).mpr
      ⟨forceMate_not_dead win, moves, by omega, by omega⟩
    have descend : ∀ (t : State), BoardStep s t → StrategyStep σ (erase s) (erase t) →
        HistoryLayer.RuleMateWithin layer σ n t := by
      intro t actual policy
      obtain ⟨m, hm, endpoint⟩ := actual
      have childWin := policy.2.2.1
      have childRank := policy.2.2.2
      have childBudget : MateWithin σ n (erase t) :=
        mateWithin_mono (strategy_rank_spec childWin).1 (by omega)
      have childClock : RawClock.clock t.val.trace + n < 100 := by
        have bound := RawClock.append_clock_le s.val m hm
        rw [endpoint]
        omega
      have cert : RawRepetition.currentOccurrences t.val < 3 ∧ LowerRankHistory σ t.val := by
        rw [endpoint]
        apply strategy_append_history s.val σ hist m hm
        · simpa only [erase, endpoint, RawTrace.erase, RawTrace.append] using childWin
        · simpa only [erase, endpoint, RawTrace.erase, RawTrace.append] using childRank
      exact ih t childBudget childClock cert.1 cert.2
    refine Or.inr ⟨ongoing, ?_⟩
    by_cases turn : (erase s).turn = σ
    · obtain ⟨r, policy⟩ := strong turn
      obtain ⟨t, actual, endpoint⟩ := layer.reply_complete ongoing policy.1
      change erase t = r at endpoint
      have childPolicy : StrategyStep σ (erase s) (erase t) := by
        rw [endpoint]
        exact policy
      exact Or.inl ⟨turn, t, actual, descend t actual childPolicy⟩
    · have other : (erase s).turn = σ.opp := by
        cases σ <;> cases h : (erase s).turn <;> simp_all [Colour.opp]
      obtain ⟨replies, all⟩ := weak other
      have noClaim : ¬CanClaim s := by
        rintro (current | ⟨m, hm, intended⟩)
        · rcases current with clock | count <;> omega
        · have legal : Legal (erase s) (play (erase s) m) := ⟨m, hm, rfl⟩
          have child := all _ legal
          have childClock := RawClock.append_clock_le s.val m hm
          have childCount := (strategy_append_history s.val σ hist m hm child.2.2.1 child.2.2.2).1
          rcases intended with clock | count <;> omega
      have someStep : ∃ t, BoardStep s t := by
        obtain ⟨r, legal⟩ := replies
        obtain ⟨t, actual, _⟩ := layer.reply_complete ongoing legal
        exact ⟨t, actual⟩
      refine Or.inr ⟨other, noClaim, someStep, ?_⟩
      intro t actual
      exact descend t actual (all _ (RawTrace.raw_step_sound actual))
end EndgameChess.Rules.RawHistoryLayer
