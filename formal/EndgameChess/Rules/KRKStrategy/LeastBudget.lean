import EndgameChess.Rules.KRKStrategy.KeyBudget
namespace EndgameChess.Rules
open EndgameChess.KK

theorem strategy_least_budget {σ : Colour} {q : Position} (h : ForceMate σ q) :
    ∃ n, MateWithin σ n q ∧ ∀ m, MateWithin σ m q → n ≤ m := by
  obtain ⟨n, hn⟩ := h
  have least : ∀ n, MateWithin σ n q →
      ∃ k, MateWithin σ k q ∧ ∀ m, MateWithin σ m q → k ≤ m := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      classical
      by_cases lower : ∃ k, k < n ∧ MateWithin σ k q
      · obtain ⟨k, hkn, hk⟩ := lower
        exact ih k hkn hk
      · exact ⟨n, hn, fun m hm => by
          by_cases bad : n ≤ m
          · exact bad
          · exact False.elim (lower ⟨m, by omega, hm⟩)⟩
  exact least n hn

end EndgameChess.Rules
