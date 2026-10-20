import EndgameChess.Rules.KRKBound.Arrival
namespace EndgameChess.Rules
open EndgameChess.KK
/-- Uniform supplied budget for EVERY canonical exact strong-turn strict wall. -/
def KRKWallBudget (σ : Colour) (B : Nat) : Prop :=
  ∀ {q : Position} {sk rs wk : EndgameChess.KK.Square}, Matches q σ ⟨sk, rs, wk, true⟩ →
    sk.2.val < rs.2.val → rs.2.val < wk.2.val → MateWithin σ B q
end EndgameChess.Rules
