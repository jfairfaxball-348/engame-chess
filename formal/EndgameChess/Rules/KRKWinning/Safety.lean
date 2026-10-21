import EndgameChess.Rules.KRKWinning.Policy
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- F gives prefix outcome/claim safety; a separate horizon is still required. -/
theorem winning_safety {c : Colour} {s : State} (win : F c s) :
    ∃ π : Policy, LegalPolicy c π ∧ WinningSafety c π s := by
  obtain ⟨π,legal,choices⟩ := winning_policy c
  have invariant : ∀ {n root t}, PolicyPath c π n root t → F c root → F c t := by
    intro n root t path
    induction path with
    | refl => intro h; exact h
    | @cons n root u t edge compatible tail ih =>
      intro rootWin
      have ongoing := KRKTermination.step_parent_ongoing edge
      have childWin : F c u := by
        rcases colour_cases c (erase root).turn with own | opponent
        · obtain ⟨v,value,_,preserve⟩ := choices root ongoing own
          have equal : v = u := Option.some.inj (value.symm.trans (compatible own))
          exact equal ▸ preserve rootWin
        · exact (forcing_actions ongoing rootWin).2 opponent |>.2 u edge
      exact ih childWin
  refine ⟨π,legal,?_⟩
  intro n t path
  have nextWin := invariant path win
  refine ⟨fun terminal => (KRKHighClock.terminal_force_iff_goal terminal).mp nextWin,?_⟩
  intro ongoing
  constructor
  · intro own none
    obtain ⟨u,value,_,_⟩ := choices t ongoing own
    rw [none] at value
    cases value
  · intro opponent
    exact ((forcing_actions ongoing nextWin).2 opponent).1
end EndgameChess.Rules.KRKWinning
