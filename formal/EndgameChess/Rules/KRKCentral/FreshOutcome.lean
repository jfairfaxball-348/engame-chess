import EndgameChess.Rules.KRKCentral.FreshWeak
import EndgameChess.Rules.KRKForcing.OutcomeClassification

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning

/-- Complete explicit winning criterion on BOTH turns of every admitted
clock-zero KRK history. Positive clocks and full FIDE correspondence remain
separate. The result refers to the independent actual winning-policy semantics. -/
theorem fresh_outcome (s : State) (σ : Colour) {sk rs wk : Square}
    (hk : IsKRK (erase s) σ sk rs wk) (zero : RawClock.clock s.val.trace=0) :
    ActualWin σ s ↔ (erase s).turn=σ ∨ MatedK (erase s) ∨
      (SafeRook sk rs wk ∧ ∃ r, Legal (erase s) r) := by
  have region : KRKTermination.Region σ s := Or.inl ⟨sk,rs,wk,hk⟩
  have arrival : ∃ p, Legal p (erase s) := by
    rcases s with ⟨⟨q,trace⟩,admitted⟩
    cases trace with
    | start => exact False.elim (initial_not_KRK σ sk rs wk hk)
    | @snoc q prior m hm => exact ⟨q,m,hm,rfl⟩
  constructor
  · intro actual
    obtain ⟨n,hn⟩ := (actual_win_iff_force region).mp actual
    have win : ForceMate σ (erase s) := ⟨n,raw_ruleMateWithin_project s σ n hn⟩
    rcases colour_cases σ (erase s).turn with ht | ht
    · exact Or.inl ht
    · exact Or.inr ((krk_weak_force_safe_iff hk ht).mp win)
  · intro criterion
    rcases colour_cases σ (erase s).turn with ht | ht
    · exact (fresh_arrival97 s σ hk ht arrival zero).2
    · have weakCriterion : MatedK (erase s) ∨ (SafeRook sk rs wk ∧ ∃ r, Legal (erase s) r) := by
        rcases criterion with same | other
        · exact False.elim (opp_ne σ (same.symm.trans ht))
        · exact other
      exact (fresh_weak98 s σ hk ht ((krk_weak_force_safe_iff hk ht).mpr weakCriterion) zero).2

end EndgameChess.Rules.KRKCentral
