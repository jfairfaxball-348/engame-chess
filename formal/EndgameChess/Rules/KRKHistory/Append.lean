import EndgameChess.Rules.KRKHistory.Definitions
namespace EndgameChess.Rules.RawHistoryLayer
open EndgameChess.KK

/-- One actual descending append keeps incoming lower counts and bounds its NEW key. -/
theorem strategy_append_history (s : RawTrace.State) (σ : Colour)
    (hist : LowerRankHistory σ s) (m : Move)
    (hm : isLegal (RawTrace.erase s) m = true)
    (win : ForceMate σ (play (RawTrace.erase s) m))
    (lower : strategyRank σ (play (RawTrace.erase s) m) < strategyRank σ (RawTrace.erase s)) :
    RawRepetition.currentOccurrences (RawTrace.append s m hm) < 3 ∧
    LowerRankHistory σ (RawTrace.append s m hm) := by
  classical
  have childCount := hist _ win lower
  refine ⟨?_, ?_⟩
  · rw [RawRepetition.append_currentOccurrences]
    omega
  · intro r rwins rlower
    have fromParent : strategyRank σ r < strategyRank σ (RawTrace.erase s) := by
      exact Nat.lt_trans rlower lower
    have oldCount := hist r rwins fromParent
    have different : RawRepetition.key (play (RawTrace.erase s) m) ≠ RawRepetition.key r := by
      intro same
      have equal := strategy_rank_key (σ := σ) same
      change strategyRank σ r < strategyRank σ (play (RawTrace.erase s) m) at rlower
      omega
    change RawOccurrences.occurrences RawRepetition.key
      (RawTrace.append s m hm).trace (RawRepetition.key r) < 2
    rw [RawOccurrences.append_occurrences]
    simp only [different, ↓reduceIte, Nat.add_zero]
    exact oldCount
end EndgameChess.Rules.RawHistoryLayer
