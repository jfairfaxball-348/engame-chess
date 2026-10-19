import EndgameChess.Rules.Outcome

/-! Clock-free, repetition-free finite-rank forced mate, S024.
The winner chooses; the defender has nonempty replies, all winning.
The budget is in plies. This is a game definition, not a FIDE WDL encoding. -/
namespace EndgameChess.Rules
open EndgameChess.KK

def MateGoal (σ : Colour) (q : Position) : Prop := q.turn = σ.opp ∧ MatedK q

/-- Finite-rank alternating attractor. Deadness stops play. Nonempty defending
replies prevent stalemate from satisfying the recursive winning clause. -/
def MateWithin (σ : Colour) : Nat → Position → Prop
  | 0, q => MateGoal σ q
  | n + 1, q => MateGoal σ q ∨ (¬ DeadK q ∧
      ((q.turn = σ ∧ ∃ r, Legal q r ∧ MateWithin σ n r) ∨
       (q.turn = σ.opp ∧ (∃ r, Legal q r) ∧ ∀ r, Legal q r → MateWithin σ n r)))

/-- Forced mate with a uniform finite ply bound; no clocks or repetition history. -/
def ForceMate (σ : Colour) (q : Position) : Prop := ∃ n, MateWithin σ n q

end EndgameChess.Rules
