import EndgameChess.Rules.KRKFresh.Definitions
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK

/-- Restricted actual descending append preserves full incoming counts for future KRK. -/
theorem restricted_append (s : RawTrace.State) (σ : Colour) (hist : History σ s)
    (m : Move) (hm : isLegal (RawTrace.erase s) m = true)
    (query : Query σ (play (RawTrace.erase s) m))
    (win : ForceMate σ (play (RawTrace.erase s) m))
    (lower : strategyRank σ (play (RawTrace.erase s) m) < strategyRank σ (RawTrace.erase s)) :
    RawRepetition.currentOccurrences (RawTrace.append s m hm) < 3 ∧
      History σ (RawTrace.append s m hm) := by
  classical
  have childCount := hist _ query win lower
  refine ⟨?_,?_⟩
  · rw [RawRepetition.append_currentOccurrences]
    omega
  · intro r rquery rwins rlower
    have fromParent := Nat.lt_trans rlower lower
    have old := hist r rquery rwins fromParent
    have different : RawRepetition.key (play (RawTrace.erase s) m) ≠ RawRepetition.key r := by
      intro same
      have equal := strategy_rank_key (σ := σ) same
      change strategyRank σ r < strategyRank σ (play (RawTrace.erase s) m) at rlower
      omega
    change RawOccurrences.occurrences RawRepetition.key (RawTrace.append s m hm).trace (RawRepetition.key r) < 2
    rw [RawOccurrences.append_occurrences]
    simp only [different,↓reduceIte,Nat.add_zero]
    exact old
end EndgameChess.Rules.KRKFresh
