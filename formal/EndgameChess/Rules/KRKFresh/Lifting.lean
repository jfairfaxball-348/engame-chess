import EndgameChess.Rules.KRKFresh.Append
import EndgameChess.Rules.KRKFresh.WinningMaterial
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK RawHistoryLayer

/-- Same supplied budget with ONLY KRK-restricted incoming rank counts. -/
theorem restricted_lifting (s : State) (σ : Colour) (n : Nat)
    (material : Query σ (erase s)) (winning : MateWithin σ n (erase s))
    (clockBudget : RawClock.clock s.val.trace + n < 100)
    (rootCount : RawRepetition.currentOccurrences s.val < 3) (hist : History σ s.val) :
    HistoryLayer.RuleMateWithin layer σ n s := by
  induction n generalizing s with
  | zero => exact winning
  | succ n ih =>
    by_cases goal : MateGoal σ (erase s)
    · exact Or.inl goal
    have win : ForceMate σ (erase s) := ⟨n+1,winning⟩
    have rankBound := (strategy_rank_spec win).2.1 (n+1) winning
    obtain ⟨strong,weak⟩ := strategy_progress win goal
    have moves : ∃ r, Legal (erase s) r := by
      rcases colour_cases σ (erase s).turn with turn | turn
      · obtain ⟨r,step⟩ := strong turn
        exact ⟨r,step.1⟩
      · exact (weak turn).1
    have ongoing : Ongoing s := (RawAdjudication.ongoing_iff s.val).mpr
      ⟨forceMate_not_dead win,moves,by omega,by omega⟩
    have descend : ∀ t : State, BoardStep s t → StrategyStep σ (erase s) (erase t) →
        HistoryLayer.RuleMateWithin layer σ n t := by
      intro t actual policy
      obtain ⟨m,hm,endpoint⟩ := actual
      have erased : erase t = play (erase s) m := by
        change RawTrace.erase t.val = _
        rw [endpoint]
        rfl
      have childWin := policy.2.2.1
      have childRank := policy.2.2.2
      have childQuery : Query σ (erase t) := by
        rw [erased]
        exact winning_move_material material hm (by rwa [←erased])
      have childBudget : MateWithin σ n (erase t) :=
        mateWithin_mono (strategy_rank_spec childWin).1 (by omega)
      have childClock : RawClock.clock t.val.trace + n < 100 := by
        have bound := RawClock.append_clock_le s.val m hm
        rw [endpoint]
        omega
      have cert : RawRepetition.currentOccurrences t.val < 3 ∧ History σ t.val := by
        rw [endpoint]
        apply restricted_append s.val σ hist m hm
        · simpa only [erase,endpoint,RawTrace.erase,RawTrace.append] using childQuery
        · simpa only [erase,endpoint,RawTrace.erase,RawTrace.append] using childWin
        · simpa only [erase,endpoint,RawTrace.erase,RawTrace.append] using childRank
      exact ih t childQuery childBudget childClock cert.1 cert.2
    refine Or.inr ⟨ongoing,?_⟩
    by_cases turn : (erase s).turn = σ
    · obtain ⟨r,policy⟩ := strong turn
      obtain ⟨t,actual,endpoint⟩ := layer.reply_complete ongoing policy.1
      change erase t = r at endpoint
      have childPolicy : StrategyStep σ (erase s) (erase t) := by rw [endpoint];exact policy
      exact Or.inl ⟨turn,t,actual,descend t actual childPolicy⟩
    · have other : (erase s).turn = σ.opp := by
        rcases colour_cases σ (erase s).turn with same | opposite
        · exact False.elim (turn same)
        · exact opposite
      obtain ⟨replies,all⟩ := weak other
      have noClaim : ¬CanClaim s := by
        rintro (current | ⟨m,hm,intended⟩)
        · rcases current with clock | count <;> omega
        · have child := all _ (show Legal (erase s) (play (erase s) m) from ⟨m,hm,rfl⟩)
          have childQuery := winning_move_material material hm child.2.2.1
          have childClock := RawClock.append_clock_le s.val m hm
          have childCount := (restricted_append s.val σ hist m hm childQuery child.2.2.1 child.2.2.2).1
          rcases intended with clock | count <;> omega
      have someStep : ∃ t, BoardStep s t := by
        obtain ⟨r,legal⟩ := replies
        obtain ⟨t,actual,_⟩ := layer.reply_complete ongoing legal
        exact ⟨t,actual⟩
      refine Or.inr ⟨other,noClaim,someStep,?_⟩
      intro t actual
      exact descend t actual (all _ (RawTrace.raw_step_sound actual))
end EndgameChess.Rules.KRKFresh
