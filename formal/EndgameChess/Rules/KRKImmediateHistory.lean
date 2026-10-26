import EndgameChess.Rules.KRKImmediate
import EndgameChess.Rules.KRKHighClock.Distance
import EndgameChess.Rules.KRKWinning.Equivalence

namespace EndgameChess.Rules.KRKImmediate
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning KRKHighClock

/-- On admitted strong-turn histories, initial-rootedness discharges the
nonchecking and king-separation hypotheses of the analytic board formula. -/
theorem admitted_immediate_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) :
    (∃ t, BoardStep s t ∧ G σ t) ↔ MateNow sk rs wk := by
  have arrival : ∃ p, Legal p (erase s) := by
    rcases s with ⟨⟨q, trace⟩, admitted⟩
    cases trace with
    | start => exact False.elim (initial_not_KRK σ sk rs wk material)
    | @snoc q prior m hm => exact ⟨q, m, hm, rfl⟩
  obtain ⟨p, legal⟩ := arrival
  obtain ⟨far, notCheck⟩ := krk_strong_arrival_geometry legal material turn
  rw [←immediate_iff material turn far notCheck]
  constructor
  · rintro ⟨t, edge, goal⟩
    exact ⟨erase t, layer.step_sound ongoing edge, goal⟩
  · rintro ⟨r, step, goal⟩
    obtain ⟨t, edge, endpoint⟩ := layer.reply_complete ongoing step
    change erase t = r at endpoint
    exact ⟨t, edge, by change MateGoal σ (erase t); rwa [endpoint]⟩

/-- Exact evaluated high-clock criterion, on the same full incoming history. -/
theorem high_clock_force_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 98 ≤ RawClock.clock s.val.trace) :
    F σ s ↔ MateNow sk rs wk :=
  (strong_high_clock_iff material ongoing turn high).trans
    (admitted_immediate_iff material ongoing turn)

theorem high_clock_actual_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 98 ≤ RawClock.clock s.val.trace) :
    ActualWin σ s ↔ MateNow sk rs wk :=
  (actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

/-- Matching defender policy: failure of the coordinate formula really allows
the weak side to hold, against every legal strong move, including castling. -/
theorem high_clock_hold_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 98 ≤ RawClock.clock s.val.trace) :
    RuleHold σ.opp s ↔ ¬MateNow sk rs wk := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high] using dual

end EndgameChess.Rules.KRKImmediate
