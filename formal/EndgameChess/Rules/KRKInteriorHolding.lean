import EndgameChess.Rules.KRKInteriorLowerBound
import EndgameChess.Rules.KRKHighClock.StrongHold

namespace EndgameChess.Rules.KRKFourPlyEscape
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning KRKHighClock KRKEdgeDepth

/-- Necessary clock inequality using the sharpened interior depth bound,
retaining the entire incoming history without freshness assumptions. -/
theorem clock_depth_necessary {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (inside : 0 < depth wk)
    (win : F σ s) :
    RawClock.clock s.val.trace + 2 * depth wk +
      (if (erase s).turn = σ then 5 else 4) ≤ 100 := by
  have arrival : ∃ p, Legal p (erase s) := by
    rcases s with ⟨⟨q, trace⟩, admitted⟩
    cases trace with
    | start => exact False.elim (initial_not_KRK σ sk rs wk material)
    | @snoc q prior m hm => exact ⟨q, m, hm, rfl⟩
  obtain ⟨p, legal⟩ := arrival
  have far := arrival_far legal material
  have deadline := (KRKDeadline.winning_deadline material win).2
  have lower := mate_depth_lower material far inside deadline
  rcases colour_cases σ (erase s).turn with strong | weak
  · have bound := lower.1 strong
    simp only [KRKDeadline.budget, strong, ↓reduceIte] at bound ⊢
    omega
  · have notStrong : (erase s).turn ≠ σ := fun h => opp_ne σ (h.symm.trans weak)
    have bound := lower.2 weak
    simp only [KRKDeadline.budget, notStrong, ↓reduceIte] at bound ⊢
    omega

/-- Explicit full-history drawing region with holding policies for both
players. In the first inward band it applies at strong h>=94 / weak h>=95. -/
theorem clock_depth_holding {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (inside : 0 < depth wk)
    (late : 100 < RawClock.clock s.val.trace + 2 * depth wk +
      (if (erase s).turn = σ then 5 else 4)) :
    RuleHold σ s ∧ RuleHold σ.opp s ∧ ¬ActualWin σ s := by
  have noWin : ¬F σ s := by
    intro win
    have bound := clock_depth_necessary material inside win
    omega
  have region : KRKTermination.Region σ s := Or.inl ⟨sk, rs, wk, material⟩
  refine ⟨strong_hold material, ?_, ?_⟩
  · apply (holding_iff_not_force region).mpr
    simpa only [opp_opp] using noWin
  · intro actual
    exact noWin ((actual_win_iff_force region).mp actual)

end EndgameChess.Rules.KRKFourPlyEscape
