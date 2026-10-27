import EndgameChess.Rules.KRKSecondOppositionHistory
import EndgameChess.Rules.KRKFourPlySecond
import EndgameChess.Rules.KRKInteriorLowerBound
import EndgameChess.Rules.KRKHighClock.StrongHold

namespace EndgameChess.Rules.KRKSecondWeakBand
open EndgameChess.KK RawHistoryLayer KRKHolding KRKLastReply KRKThreePly
open KRKOppositionHistory KRKSecondOppositionHistory

/-- The complete evaluated winning formula at the second edge file for
ongoing weak-turn h>=95 histories. All counts query the original trace. -/
def SecondBandClear (s : RawTrace.State) (sk rs wk : Square) (high : wk.1.val ≤ 4) : Prop :=
  (LastReply sk rs wk ∧ RawClock.clock s.trace < 99 ∧
    RawRepetition.currentOccurrences s < 3 ∧
    RawRepetition.occurrences s.trace (play (RawTrace.erase s) ⟨wk, (sk.1, 0), none⟩) < 2) ∨
  (sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ 3 ≤ rs.2.val ∧ SecondClear s sk rs wk high)

private theorem admitted_far {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) : 2 ≤ dInf sk wk := by
  have arrival : ∃ p, Legal p (erase s) := by
    rcases s with ⟨⟨q, trace⟩, admitted⟩
    cases trace with
    | start => exact False.elim (initial_not_KRK σ sk rs wk material)
    | @snoc q prior m hm => exact ⟨q, m, hm, rfl⟩
  obtain ⟨p, legal⟩ := arrival
  exact KRKEdgeDepth.arrival_far legal material

private theorem last_return_legal {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (high : wk.1.val ≤ 4)
    (last : LastReply sk rs wk) : isLegal q ⟨wk, (sk.1, 0), none⟩ = true := by
  obtain ⟨sy, ry, sides⟩ := (last_middle_iff rank (by omega) (by omega)).mp last
  apply lone_step_legal material turn
  refine StepM.lone ?_ ?_ ?_ ?_
  · simp [dInf, absDiff, rank]; omega
  · rw [ne_iff_coords]; dsimp only; omega
  · simp [dInf, absDiff, sy]
  · simp [RookSees, RookLine]; omega

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (high : wk.1.val ≤ 4) :
    F σ s ↔ SecondBandClear s.val sk rs wk high := by
  have far := admitted_far material
  constructor
  · intro win
    have deadline := (KRKDeadline.winning_deadline material win).2
    have notStrong : (erase s).turn ≠ σ := fun h => opp_ne σ (h.symm.trans turn)
    have budget : KRKDeadline.budget σ s ≤ 5 := by
      simp only [KRKDeadline.budget, notStrong, ↓reduceIte]; omega
    have four := KRKFourPlyEscape.weak_five_to_four material turn (mateWithin_mono deadline budget)
    rcases (KRKFourPlySecond.weak_four_iff material turn far rank file).mp four with mate | last | ⟨sx, sy, ry⟩
    · exact False.elim (mate.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1))
    · have legal := last_return_legal material turn rank file high last
      have absent := weak_force_no_claim ongoing turn win
      exact Or.inl ⟨last, (no_claim_at_unique_reply material turn far last legal).mp absent⟩
    · exact Or.inr ⟨sx, sy, ry,
        (KRKSecondOppositionHistory.high_clock_force_iff material ongoing turn highClock rank file high (by omega) sy ry).mp win⟩
  · rintro (⟨last, clock, count, child⟩ | ⟨sx, sy, ry, clear⟩)
    · have legal := last_return_legal material turn rank file high last
      have absent := (no_claim_at_unique_reply material turn far last legal).mpr ⟨clock, count, child⟩
      exact ⟨2, (rule_two_iff material ongoing turn).mpr ⟨last, absent⟩⟩
    · exact (KRKSecondOppositionHistory.high_clock_force_iff material ongoing turn highClock rank file high (by omega) sy ry).mpr clear

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (high : wk.1.val ≤ 4) :
    KRKWinning.ActualWin σ s ↔ SecondBandClear s.val sk rs wk high :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn highClock rank file high)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (high : wk.1.val ≤ 4) :
    RuleHold σ.opp s ↔ ¬SecondBandClear s.val sk rs wk high := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn highClock rank file high] using dual

/-- Both players can hold exactly on the complement of the evaluated
winning region in this band. -/
theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (high : wk.1.val ≤ 4) :
    (RuleHold σ s ∧ RuleHold σ.opp s) ↔ ¬SecondBandClear s.val sk rs wk high := by
  constructor
  · intro holds
    exact (high_clock_hold_iff material ongoing turn highClock rank file high).mp holds.2
  · intro outside
    exact ⟨KRKHighClock.strong_hold material,
      (high_clock_hold_iff material ongoing turn highClock rank file high).mpr outside⟩

private theorem weak_not_one {s : State} {σ : Colour} (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) : ¬W σ 1 s := by
  intro cert
  have board := raw_ruleMateWithin_project s σ 1 cert
  rcases board with goal | ⟨_, chosen | defended⟩
  · exact goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
  · exact opp_ne σ (chosen.1.symm.trans turn)
  · obtain ⟨r, legal⟩ := defended.2.1
    have goal := defended.2.2 r legal
    have strong : r.turn = σ := by rw [turn_of_legal legal, turn, opp_opp]
    exact opp_ne σ (strong.symm.trans goal.1)

/-- Winning distances in this whole band are evaluated: two plies in
LastReply and four in the disjoint opposition family. -/
theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (high : wk.1.val ≤ 4) (win : F σ s) :
    (LastReply sk rs wk ∧ W σ 2 s ∧ ¬W σ 1 s) ∨
      (¬LastReply sk rs wk ∧ W σ 4 s ∧ ¬W σ 3 s) := by
  rcases (high_clock_force_iff material ongoing turn highClock rank file high).mp win with
    ⟨last, clock, count, child⟩ | ⟨sx, sy, ry, clear⟩
  · have legal := last_return_legal material turn rank file high last
    have noClaim := (no_claim_at_unique_reply material turn (admitted_far material) last legal).mpr ⟨clock, count, child⟩
    exact Or.inl ⟨last, (rule_two_iff material ongoing turn).mpr ⟨last, noClaim⟩, weak_not_one ongoing turn⟩
  · have notLast : ¬LastReply sk rs wk := by
      intro last
      obtain ⟨_, _, sides⟩ := (last_middle_iff rank (by omega) (by omega)).mp last
      omega
    exact Or.inr ⟨notLast, second_sufficient material ongoing turn highClock rank file high (by omega) sy ry clear,
      (KRKSecondOppositionHistory.high_clock_exact_four material ongoing turn highClock rank file high (by omega) sy ry).2⟩

end EndgameChess.Rules.KRKSecondWeakBand
