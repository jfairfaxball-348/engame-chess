import EndgameChess.Rules.KRKBound.Defend
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

theorem mateWithin_pair {σ : Colour} {q c : Position} {n : Nat}
    (ht : q.turn = σ) (hl : Legal q c) (hc : c.turn = σ.opp)
    (hne : ∃ r, Legal c r) (hall : ∀ r, Legal c r → MateWithin σ n r) :
    MateWithin σ (n + 2) q :=
  mateWithin_choose ht hl (mateWithin_defend hc hne hall)
end EndgameChess.Rules
