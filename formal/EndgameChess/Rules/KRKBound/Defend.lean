import EndgameChess.Rules.KRKBound.Choose
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

theorem mateWithin_defend {σ : Colour} {q : Position} {n : Nat}
    (ht : q.turn = σ.opp) (hne : ∃ r, Legal q r)
    (hall : ∀ r, Legal q r → MateWithin σ n r) : MateWithin σ (n + 1) q := by
  have hd := forceMate_not_dead (forceMate_defend ht hne (fun r hr => ⟨n, hall r hr⟩))
  exact Or.inr ⟨hd, Or.inr ⟨ht, hne, hall⟩⟩
end EndgameChess.Rules
