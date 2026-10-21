import EndgameChess.Rules.KRKFresh.Definitions
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Any earlier KRK occurrence propagates through actual typed admitted Region. -/
theorem prefix_region {σ : Colour} {q : Position} (trace : RawTrace.Trace q)
    (admitted : StoppedHistory.Admissible trace) (ever : Ever σ trace) :
    Region σ (⟨⟨q,trace⟩,admitted⟩ : State) := by
  induction trace with
  | start =>
    obtain ⟨p,member,sk,rs,wk,material⟩ := ever
    have same : p = initial := by simpa only [RawTrace.Trace.positions,List.mem_singleton] using member
    subst p
    exact False.elim (initial_not_KRK σ sk rs wk material)
  | @snoc q prior m hm ih =>
    obtain ⟨p,member,query⟩ := ever
    simp only [RawTrace.Trace.positions,List.mem_append,List.mem_singleton] at member
    rcases member with earlier | rfl
    · have parent := ih admitted.1 ⟨p,earlier,query⟩
      have edge : BoardStep (⟨⟨q,prior⟩,admitted.1⟩ : State)
          (⟨⟨play q m,.snoc prior m hm⟩,admitted⟩ : State) := ⟨m,hm,rfl⟩
      exact (step_decreases parent edge).1
    · exact Or.inl query
end EndgameChess.Rules.KRKFresh
