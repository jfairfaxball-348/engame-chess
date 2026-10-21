import EndgameChess.Rules.KRKWinning.Actions
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- Globally legal full-history choices preserve F and never choose an own claim. -/
theorem winning_policy (c : Colour) : ∃ π : Policy, LegalPolicy c π ∧
    ∀ s, Ongoing s → (erase s).turn = c →
      ∃ t, π s = some t ∧ BoardStep s t ∧ (F c s → F c t) := by
  classical
  let Choice (s : State) (a : Option State) : Prop :=
    Ongoing s → (erase s).turn = c →
      ∃ t, a = some t ∧ BoardStep s t ∧ (F c s → F c t)
  have existsChoice : ∀ s, ∃ a, Choice s a := by
    intro s
    by_cases ongoing : Ongoing s
    · by_cases own : (erase s).turn = c
      · by_cases win : F c s
        · obtain ⟨t,edge,child⟩ := (forcing_actions ongoing win).1 own
          exact ⟨some t,fun _ _ => ⟨t,rfl,edge,fun _ => child⟩⟩
        · obtain ⟨r,move⟩ := ((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1
          obtain ⟨t,edge,_⟩ := layer.reply_complete ongoing move
          exact ⟨some t,fun _ _ => ⟨t,rfl,edge,fun bad => False.elim (win bad)⟩⟩
      · exact ⟨none,fun _ bad => False.elim (own bad)⟩
    · exact ⟨none,fun bad => False.elim (ongoing bad)⟩
  let π : Policy := fun s => Classical.choose (existsChoice s)
  have choices : ∀ s, Choice s (π s) := fun s => Classical.choose_spec (existsChoice s)
  refine ⟨π,?_,choices⟩
  intro s ongoing own
  obtain ⟨t,value,edge,_⟩ := choices s ongoing own
  rw [value]
  exact edge
end EndgameChess.Rules.KRKWinning
