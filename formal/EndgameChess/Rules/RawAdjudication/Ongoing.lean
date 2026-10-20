import EndgameChess.Rules.RawAdjudication.Definitions

/-! S060 / EC-C036: exact raw ongoing guards retain legal reply existence. -/
namespace EndgameChess.Rules.RawAdjudication

/-- Ongoing means nondead with legal moves and no automatic numeric trigger. -/
theorem ongoing_iff (s : RawTrace.State) :
    classify s = .ongoing ↔
      ¬DeadK (RawTrace.erase s) ∧ (∃ r, Legal (RawTrace.erase s) r) ∧
      RawClock.clock s.trace < 150 ∧ RawRepetition.currentOccurrences s < 5 := by
  classical
  constructor
  · intro ongoing
    have notMate : ¬MatedK (RawTrace.erase s) := by
      intro mate
      simp [classify, mate] at ongoing
    have notDraw : ¬DrawTrigger s := by
      intro draw
      simp [classify, notMate, draw] at ongoing
    have notDead : ¬DeadK (RawTrace.erase s) :=
      fun dead => notDraw (Or.inr (Or.inl dead))
    have moves : ∃ r, Legal (RawTrace.erase s) r := by
      apply Classical.byContradiction
      intro none
      by_cases check : inCheck (RawTrace.erase s) (RawTrace.erase s).turn = true
      · exact notMate ⟨check, none⟩
      · have noCheck : inCheck (RawTrace.erase s) (RawTrace.erase s).turn = false :=
          Bool.eq_false_iff.mpr check
        exact notDraw (Or.inl ⟨noCheck, none⟩)
    refine ⟨notDead, moves, ?_, ?_⟩
    · apply Nat.lt_of_not_ge
      intro clock
      exact notDraw (Or.inr (Or.inr (Or.inl clock)))
    · apply Nat.lt_of_not_ge
      intro count
      exact notDraw (Or.inr (Or.inr (Or.inr count)))
  · rintro ⟨notDead, moves, clock, count⟩
    have notMate : ¬MatedK (RawTrace.erase s) := fun mate => mate.2 moves
    have notDraw : ¬DrawTrigger s := by
      intro draw
      rcases draw with stale | dead | long | repeated
      · exact stale.2 moves
      · exact notDead dead
      · omega
      · omega
    simp [classify, notMate, notDraw]

end EndgameChess.Rules.RawAdjudication
