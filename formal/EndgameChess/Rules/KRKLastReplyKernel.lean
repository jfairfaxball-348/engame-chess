import EndgameChess.Rules.KRKLastReply
import EndgameChess.Rules.KRKBound.Defend

namespace EndgameChess.Rules.KRKLastReply
open EndgameChess.KK KRKMateGeometry KRKImmediate

private theorem strong_one_iff {q : Position} {σ : Colour} (turn : q.turn = σ) :
    MateWithin σ 1 q ↔ ∃ r, Legal q r ∧ MateGoal σ r := by
  constructor
  · intro win
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
    · exact chosen.2
    · exact False.elim (opp_ne σ (turn.symm.trans defended.1))
  · rintro ⟨r, legal, goal⟩
    exact mateWithin_choose turn legal goal

/-- Exact evaluated two-ply criterion, on actual weak-turn kernel boards.
The terminal mate clause is separate; all rook captures are retained. -/
theorem weak_two_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) :
    MateWithin σ 2 q ↔ MatedK q ∨ LastReply sk rs wk := by
  constructor
  · intro win
    have safe := krk_force_weak_safe material turn ⟨2, win⟩
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact Or.inl goal.2
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · right
      apply (model_last_iff far).mp
      refine ⟨safe, ?_, ?_⟩
      · obtain ⟨r, legal⟩ := defended.2.1
        obtain ⟨t, _, step⟩ := krk_safe_reply material turn safe legal
        exact ⟨t, step⟩
      · intro t step
        obtain ⟨r, legal, next⟩ := step_sound
          (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
        obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry legal next.1 next.2
        exact (immediate_iff next.1 next.2 nextFar notCheck).mp
          ((strong_one_iff next.2).mp (defended.2.2 r legal))
  · rintro (mate | geometry)
    · exact mateWithin_mono (show MateWithin σ 0 q from ⟨turn, mate⟩) (by omega)
    · obtain ⟨safe, ⟨t, step⟩, every⟩ := (model_last_iff far).mpr geometry
      obtain ⟨r, legal, _⟩ := step_sound
        (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
      apply mateWithin_defend turn ⟨r, legal⟩
      intro u reply
      obtain ⟨w, next, move⟩ := krk_safe_reply material turn safe reply
      obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry reply next.1 next.2
      apply (strong_one_iff next.2).mpr
      exact (immediate_iff next.1 next.2 nextFar notCheck).mpr (every w move)

private theorem strong_two_to_one {q : Position} {σ : Colour} (turn : q.turn = σ)
    (win : MateWithin σ 2 q) : MateWithin σ 1 q := by
  rcases win with goal | ⟨_, chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_, r, legal, child⟩ := chosen
    have nextTurn : r.turn = σ.opp := by rw [turn_of_legal legal, turn]
    have goal : MateGoal σ r := by
      rcases child with goal | ⟨_, chosen | defended⟩
      · exact goal
      · exact False.elim (opp_ne σ (chosen.1.symm.trans nextTurn))
      · obtain ⟨u, reply⟩ := defended.2.1
        have goal := defended.2.2 u reply
        have strong : u.turn = σ := by rw [turn_of_legal reply, nextTurn, opp_opp]
        exact False.elim (opp_ne σ (strong.symm.trans goal.1))
    exact mateWithin_choose turn legal goal
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

/-- Three plies give a weak-turn root no extra mating opportunity, since the
final move belongs to the strong side. The same evaluated formula applies. -/
theorem weak_three_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) :
    MateWithin σ 3 q ↔ MatedK q ∨ LastReply sk rs wk := by
  rw [←weak_two_iff material turn far]
  constructor
  · intro win
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact Or.inl goal
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · apply mateWithin_defend turn defended.2.1
      intro r legal
      have nextTurn : r.turn = σ := by rw [turn_of_legal legal, turn, opp_opp]
      exact strong_two_to_one nextTurn (defended.2.2 r legal)
  · intro win; exact mateWithin_mono win (by omega)

end EndgameChess.Rules.KRKLastReply
