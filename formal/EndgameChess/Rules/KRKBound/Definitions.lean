import EndgameChess.Rules.KRKBound.Budget
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

def LowerExitBound (σ : Colour) (y E : Nat) : Prop :=
  ∀ {q : Position} {sk rs wk : Square}, Matches q σ ⟨sk, rs, wk, true⟩ →
    sk.2.val + 1 = y → rs.2.val = y → 2 ≤ absDiff rs.1.val wk.1.val →
    (y + 2 ≤ wk.2.val ∨ (wk.2.val = y + 1 ∧ sk.1.val = wk.1.val)) →
    MateWithin σ E q
end EndgameChess.Rules
