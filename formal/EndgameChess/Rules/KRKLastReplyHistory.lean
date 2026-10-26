import EndgameChess.Rules.KRKLastReplyKernel
import EndgameChess.Rules.KRKImmediateHistory
import EndgameChess.Rules.KRKDeadline.Necessary

namespace EndgameChess.Rules.KRKLastReply
open EndgameChess.KK RawHistoryLayer KRKHolding KRKWinning KRKHighClock

private theorem admitted_far {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) : 2 ≤ dInf sk wk := by
  have arrival : ∃ p, Legal p (erase s) := by
    rcases s with ⟨⟨q, trace⟩, admitted⟩
    cases trace with
    | start => exact False.elim (initial_not_KRK σ sk rs wk material)
    | @snoc q prior m hm => exact ⟨q, m, hm, rfl⟩
  obtain ⟨p, legal⟩ := arrival
  exact KRKEdgeDepth.arrival_far legal material

/-- Exact two-ply history criterion at any clock: the evaluated board region
and absence of the defender's actual current/intended claim. -/
theorem rule_two_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) :
    W σ 2 s ↔ LastReply sk rs wk ∧ ¬CanClaim s := by
  have far := admitted_far material
  have notMate : ¬MatedK (erase s) := fun h =>
    h.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
  constructor
  · intro win
    have board := raw_ruleMateWithin_project s σ 2 win
    have geometry := ((weak_two_iff material turn far).mp board).resolve_left notMate
    refine ⟨geometry, ?_⟩
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact False.elim (notMate goal.2)
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · exact defended.2.1
  · rintro ⟨geometry, noClaim⟩
    have board := (weak_two_iff material turn far).mpr (Or.inr geometry)
    rcases board with goal | ⟨_, chosen | defended⟩
    · exact False.elim (notMate goal.2)
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · obtain ⟨r, legal⟩ := defended.2.1
      obtain ⟨t, edge, _⟩ := layer.reply_complete ongoing legal
      refine Or.inr ⟨ongoing, Or.inr ⟨turn, noClaim, ⟨t, edge⟩, ?_⟩⟩
      intro u move
      have legalMove : Legal (erase s) (erase u) := layer.step_sound ongoing move
      have child := defended.2.2 (erase u) legalMove
      have nextTurn : (erase u).turn = σ := by rw [turn_of_legal legalMove, turn, opp_opp]
      have immediate : ∃ r, Legal (erase u) r ∧ MateGoal σ r := by
        rcases child with goal | ⟨_, chosen | defended⟩
        · exact False.elim (opp_ne σ (nextTurn.symm.trans goal.1))
        · exact chosen.2
        · exact False.elim (opp_ne σ (nextTurn.symm.trans defended.1))
      have noThreshold : ¬RawClaims.CurrentThreshold u.val := by
        intro threshold
        obtain ⟨m, hm, endpoint⟩ := move
        apply noClaim
        right
        refine ⟨m, hm, ?_⟩
        rw [←endpoint]
        exact threshold
      have clock : RawClock.clock u.val.trace < 100 := by
        apply Nat.lt_of_not_ge
        intro high
        exact noThreshold (Or.inl high)
      have count : RawRepetition.currentOccurrences u.val < 3 := by
        apply Nat.lt_of_not_ge
        intro repeated
        exact noThreshold (Or.inr repeated)
      have childOngoing : Ongoing u := (RawAdjudication.ongoing_iff u.val).mpr
        ⟨forceMate_not_dead ⟨1, child⟩, ⟨immediate.choose, immediate.choose_spec.1⟩,
          by omega, by omega⟩
      obtain ⟨r, mateMove, goal⟩ := immediate
      obtain ⟨v, finalStep, endpoint⟩ := layer.reply_complete childOngoing mateMove
      change erase v = r at endpoint
      refine Or.inr ⟨childOngoing, Or.inl ⟨nextTurn, v, finalStep, ?_⟩⟩
      change MateGoal σ (erase v)
      rwa [endpoint]

/-- Complete evaluated weak-turn outcome for ongoing h>=97, retaining the
entire incoming trace through the current/intended claim predicate. -/
theorem high_clock_force_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 97 ≤ RawClock.clock s.val.trace) :
    F σ s ↔ LastReply sk rs wk ∧ ¬CanClaim s := by
  constructor
  · intro win
    have deadline := (KRKDeadline.winning_deadline material win).2
    have notStrong : (erase s).turn ≠ σ := fun h => opp_ne σ (h.symm.trans turn)
    have small : KRKDeadline.budget σ s ≤ 3 := by
      simp only [KRKDeadline.budget, notStrong, ↓reduceIte]; omega
    have board := mateWithin_mono deadline small
    have notMate : ¬MatedK (erase s) := fun h =>
      h.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
    have geometry := ((weak_three_iff material turn (admitted_far material)).mp board).resolve_left notMate
    refine ⟨geometry, ?_⟩
    obtain ⟨n, cert⟩ := win
    cases n with
    | zero => exact False.elim (notMate cert.2)
    | succ n =>
      rcases cert with goal | ⟨_, chosen | defended⟩
      · exact False.elim (notMate goal.2)
      · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
      · exact defended.2.1
  · intro h
    exact ⟨2, (rule_two_iff material ongoing turn).mpr h⟩

theorem high_clock_actual_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 97 ≤ RawClock.clock s.val.trace) :
    ActualWin σ s ↔ LastReply sk rs wk ∧ ¬CanClaim s :=
  (actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

theorem high_clock_hold_iff {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 97 ≤ RawClock.clock s.val.trace) :
    RuleHold σ.opp s ↔ ¬(LastReply sk rs wk ∧ ¬CanClaim s) := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high] using dual

/-- The winning weak-turn high-clock region has exact optimal board-ply
distance two in the RAW layer. This is not a global DTZ identification. -/
theorem high_clock_exact_two {σ : Colour} {s : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 97 ≤ RawClock.clock s.val.trace) :
    (F σ s ↔ W σ 2 s) ∧ ¬W σ 1 s := by
  constructor
  · exact (high_clock_force_iff material ongoing turn high).trans
      (rule_two_iff material ongoing turn).symm
  · intro win
    have board := raw_ruleMateWithin_project s σ 1 win
    have notMate : ¬MatedK (erase s) := fun h =>
      h.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
    rcases board with goal | ⟨_, chosen | defended⟩
    · exact notMate goal.2
    · exact opp_ne σ (chosen.1.symm.trans turn)
    · obtain ⟨r, legal⟩ := defended.2.1
      have goal := defended.2.2 r legal
      have nextTurn : r.turn = σ := by rw [turn_of_legal legal, turn, opp_opp]
      exact opp_ne σ (nextTurn.symm.trans goal.1)

end EndgameChess.Rules.KRKLastReply
