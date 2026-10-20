import EndgameChess.Rules.KRKStrategy.Progress
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Full-line pairwise key uniqueness, winning vertices, and the exact vertex-count ceiling. -/
theorem strategy_line_certificate {σ : Colour} {q : Position} {tail : List Position}
    (line : StrategyLine σ (q :: tail)) :
    ForceMate σ q ∧
    (∀ r ∈ tail, ForceMate σ r ∧ strategyRank σ r < strategyRank σ q) ∧
    List.Pairwise (fun a b => RawRepetition.key a ≠ RawRepetition.key b) (q :: tail) ∧
    (q :: tail).length ≤ strategyRank σ q + 1 := by
  let Certificate (q : Position) (tail : List Position) : Prop :=
    ForceMate σ q ∧
    (∀ r ∈ tail, ForceMate σ r ∧ strategyRank σ r < strategyRank σ q) ∧
    List.Pairwise (fun a b => RawRepetition.key a ≠ RawRepetition.key b) (q :: tail) ∧
    (q :: tail).length ≤ strategyRank σ q + 1
  have general : ∀ {xs : List Position}, StrategyLine σ xs →
      ∀ {q : Position} {tail : List Position}, xs = q :: tail → Certificate q tail := by
    intro xs line
    induction line with
    | single q win =>
      intro a rest eq
      cases eq
      change _ ∧ _ ∧ _ ∧ _
      refine ⟨win, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
    | @cons q r tail step line ih =>
      intro a rest eq
      cases eq
      change _ ∧ _ ∧ _ ∧ _
      obtain ⟨headWin, later, distinct, length⟩ := ih rfl
      have ranks : ∀ z ∈ r :: tail, ForceMate σ z ∧ strategyRank σ z < strategyRank σ q := by
        intro z hz
        rcases List.mem_cons.mp hz with same | rest
        · subst z
          exact ⟨step.2.2.1, step.2.2.2⟩
        · obtain ⟨zw, zr⟩ := later z rest
          exact ⟨zw, Nat.lt_trans zr step.2.2.2⟩
      refine ⟨step.2.1, ranks, ?_, ?_⟩
      · apply List.pairwise_cons.mpr
        refine ⟨?_, distinct⟩
        intro z hz same
        have lt := (ranks z hz).2
        have eq := strategy_rank_key (σ := σ) same
        omega
      · simp only [List.length_cons] at *
        have lt := step.2.2.2
        omega
  exact general line rfl
end EndgameChess.Rules
