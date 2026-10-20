import EndgameChess.Rules.KRKForcing.SafeSetup
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

theorem mateWithin_choose {σ : Colour} {q r : Position} {n : Nat}
    (ht : q.turn = σ) (hl : Legal q r) (hw : MateWithin σ n r) :
    MateWithin σ (n + 1) q := by
  have hd := forceMate_not_dead (forceMate_choose ht hl ⟨n, hw⟩)
  exact Or.inr ⟨hd, Or.inl ⟨ht, r, hl, hw⟩⟩
end EndgameChess.Rules
