import EndgameChess.Rules.KRKStrategy.KeyInterface
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Every supplied clock-free budget is invariant under the existing raw key. -/
theorem strategy_key_budget {q r : Position} (hk : RawRepetition.key q = RawRepetition.key r)
    (σ : Colour) (n : Nat) : MateWithin σ n q ↔ MateWithin σ n r := by
  have forward : ∀ {a b : Position}, RawRepetition.key a = RawRepetition.key b →
      MateWithin σ n a → MateWithin σ n b := by
    intro a b same win
    obtain ⟨turn, check, legal, goal⟩ := strategy_key_interface same
    cases n with
    | zero => exact (goal σ).mp win
    | succ n =>
      rcases win with mate | ⟨_, strong | weak⟩
      · exact Or.inl ((goal σ).mp mate)
      · obtain ⟨whose, c, step, child⟩ := strong
        exact mateWithin_choose (turn ▸ whose) ((legal c).mp step) child
      · obtain ⟨whose, ⟨c, step⟩, all⟩ := weak
        exact mateWithin_defend (turn ▸ whose) ⟨c, (legal c).mp step⟩
          (fun z hz => all z ((legal z).mpr hz))
  exact ⟨forward hk, forward hk.symm⟩
end EndgameChess.Rules
