import EndgameChess.Rules.KRKStrategy.Definitions
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Every winning nonmate has a descending strong choice and ALL descending weak replies. -/
theorem strategy_progress {σ : Colour} {q : Position}
    (win : ForceMate σ q) (ongoing : ¬MateGoal σ q) :
    (q.turn = σ → ∃ r, StrategyStep σ q r) ∧
    (q.turn = σ.opp → (∃ r, Legal q r) ∧ ∀ r, Legal q r → StrategyStep σ q r) := by
  obtain ⟨spec, minimal, zero⟩ := strategy_rank_spec win
  have pos : 0 < strategyRank σ q := by
    apply Classical.byContradiction
    intro h
    exact ongoing (zero.mp (by omega))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : strategyRank σ q ≠ 0)
  rw [hn] at spec
  rcases spec with goal | ⟨_, strong | weak⟩
  · exact False.elim (ongoing goal)
  · obtain ⟨turn, r, legal, child⟩ := strong
    have childWin : ForceMate σ r := ⟨n, child⟩
    have childRank := (strategy_rank_spec childWin).2.1 n child
    refine ⟨fun _ => ⟨r, legal, win, childWin, by omega⟩, ?_⟩
    intro wrong
    exact False.elim (opp_ne σ (turn.symm.trans wrong))
  · obtain ⟨turn, replies, all⟩ := weak
    refine ⟨?_, fun _ => ⟨replies, ?_⟩⟩
    · intro wrong
      exact False.elim (opp_ne σ (wrong.symm.trans turn))
    · intro r legal
      have childWin : ForceMate σ r := ⟨n, all r legal⟩
      have childRank := (strategy_rank_spec childWin).2.1 n (all r legal)
      exact ⟨legal, win, childWin, by omega⟩
end EndgameChess.Rules
