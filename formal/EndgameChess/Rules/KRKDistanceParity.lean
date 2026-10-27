import EndgameChess.Rules.KRKThreePlyHistory

namespace EndgameChess.Rules.KRKDistanceParity
open EndgameChess.KK RawHistoryLayer KRKHolding

private theorem child_turn {s t : State} (edge : BoardStep s t) : (erase t).turn = (erase s).turn.opp :=
  turn_of_legal (RawTrace.raw_step_sound edge)

theorem weak_one_goal {s : State} {σ : Colour} (turn : (erase s).turn = σ.opp)
    (cert : W σ 1 s) : G σ s := by
  rcases cert with goal | ⟨_,chosen | defended⟩
  · exact goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · obtain ⟨t,edge⟩ := defended.2.2.1
    have goal := defended.2.2.2 t edge
    have strong : (erase t).turn = σ := by rw [child_turn edge,turn,opp_opp]
    exact False.elim (opp_ne σ (strong.symm.trans goal.1))

theorem strong_two_one {s : State} {σ : Colour} (turn : (erase s).turn = σ)
    (cert : W σ 2 s) : W σ 1 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,t,edge,child⟩ := chosen
    have weak : (erase t).turn = σ.opp := by rw [child_turn edge,turn]
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,weak_one_goal weak child⟩⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem weak_three_two {s : State} {σ : Colour} (turn : (erase s).turn = σ.opp)
    (cert : W σ 3 s) : W σ 2 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · refine Or.inr ⟨ongoing,Or.inr ⟨turn,defended.2.1,defended.2.2.1,?_⟩⟩
    intro t edge
    have strong : (erase t).turn = σ := by rw [child_turn edge,turn,opp_opp]
    exact strong_two_one strong (defended.2.2.2 t edge)

theorem strong_four_three {s : State} {σ : Colour} (turn : (erase s).turn = σ)
    (cert : W σ 4 s) : W σ 3 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,t,edge,child⟩ := chosen
    have weak : (erase t).turn = σ.opp := by rw [child_turn edge,turn]
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,weak_three_two weak child⟩⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

end EndgameChess.Rules.KRKDistanceParity
