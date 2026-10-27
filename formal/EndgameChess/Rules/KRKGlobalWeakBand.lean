import EndgameChess.Rules.KRKFramedPrefix
import EndgameChess.Rules.KRKCornerWeakBand

namespace EndgameChess.Rules.KRKGlobalWeakBand
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKWeakBranch RawHistoryLayer KRKHolding
open KRKNativeFrame
open KRKCornerWeakBand (Guard guard_legal step_guard)
set_option maxHeartbeats 400000

/-- At most eight neighbour guards; each surviving branch is evaluated by
seven coordinate slots and original-trace repetition tests. -/
def Clear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 99 ∧ RawRepetition.currentOccurrences s < 3 ∧
    ∀ t : Square, Guard sk rs wk t →
      RawRepetition.occurrences s.trace (firstBoard s wk t) < 2 ∧
        KRKEdgeDepth.depth t = 0 ∧ KRKFramedPrefix.Clear s (normalize t) sk rs wk t

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace) (win : F σ s) :
    Clear s.val sk rs wk := by
  have safe : SafeRook sk rs wk := by
    obtain ⟨n, cert⟩ := win
    exact krk_force_weak_safe material turn ⟨n, raw_ruleMateWithin_project s σ n cert⟩
  obtain ⟨noClaim, nonempty, all⟩ := weak_force_data ongoing turn win
  have claims := (RawClaims.no_threshold_iff s.val).mp noClaim
  have time : RawClock.clock s.val.trace < 99 := by
    obtain ⟨v, m, legal, _⟩ := nonempty
    have bound := (claims.2.2 m legal).1
    have quiet := weak_safe_quiet material turn safe legal
    change (if RawClock.zeroing (erase s) m then 0 else RawClock.clock s.val.trace + 1) < 100 at bound
    simp only [quiet, Bool.false_eq_true, ↓reduceIte] at bound
    omega
  refine ⟨safe, time, claims.2.1, ?_⟩
  intro t guard
  have legal := guard_legal material turn guard
  have childWin := all (weakChild s ongoing wk t legal) ⟨_, legal, rfl⟩
  have history := child_history_of_force material ongoing turn safe high legal childWin
  have depth := KRKFourPlyEscape.three_depth_zero (history_geometry history)
  have normal := normalize_spec depth
  exact ⟨(claims.2.2 _ legal).2, depth,
    (KRKFramedPrefix.history_append_iff (normalize t) material turn safe legal normal.1 normal.2).mp history⟩

theorem sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (clear : Clear s.val sk rs wk) : W σ 4 s := by
  have safe := clear.1
  have time := clear.2.1
  have branches := clear.2.2.2
  have noClaim : ¬CanClaim s := by
    apply (RawClaims.no_threshold_iff s.val).mpr
    refine ⟨by omega, clear.2.2.1, ?_⟩
    intro m legal
    obtain ⟨t, next, step⟩ := krk_safe_reply material turn safe ⟨m, legal, rfl⟩
    have canonical := weak_move_eq material turn legal next.1
    have guard := step_guard step
    constructor
    · have bound := RawClock.append_clock_le s.val m legal
      omega
    · rw [canonical]
      exact (branches t guard).1
  have nonempty : ∃ v, BoardStep s v := by
    obtain ⟨q, m, legal, _⟩ := ((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1
    let v : State := ⟨RawTrace.append s.val m legal,
      ((StoppedHistory.append_and_reply_lifting s.val).1 m legal).mpr ⟨s.property, ongoing⟩⟩
    exact ⟨v, m, legal, rfl⟩
  refine Or.inr ⟨ongoing, Or.inr ⟨turn, noClaim, nonempty, ?_⟩⟩
  intro v edge
  obtain ⟨m, legal, rawEq⟩ := edge
  obtain ⟨t, next, step⟩ := krk_safe_reply material turn safe ⟨m, legal, rfl⟩
  have canonical := weak_move_eq material turn legal next.1
  have childLegal : isLegal (erase s) ⟨wk, t, none⟩ = true := by rwa [←canonical]
  have childEq : v = weakChild s ongoing wk t childLegal := by
    apply Subtype.ext
    simpa only [weakChild, canonical] using rawEq
  rw [childEq]
  have branch := branches t (step_guard step)
  have normal := normalize_spec branch.2.1
  have history := (KRKFramedPrefix.history_append_iff (normalize t) material turn safe childLegal normal.1 normal.2).mpr branch.2.2
  exact child_certificate material ongoing turn safe childLegal time branch.1 history

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace) :
    F σ s ↔ Clear s.val sk rs wk := by
  constructor
  · exact necessary material ongoing turn high
  · intro clear; exact ⟨4, sufficient material ongoing turn clear⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
 :
    KRKWinning.ActualWin σ s ↔ Clear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn highClock)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
 :
    RuleHold σ.opp s ↔ ¬Clear s.val sk rs wk := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn highClock] using dual

/-- Both players can hold exactly on the complement of the evaluated
winning region in this band. -/
theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
 :
    (RuleHold σ s ∧ RuleHold σ.opp s) ↔ ¬Clear s.val sk rs wk := by
  constructor
  · intro holds
    exact (high_clock_hold_iff material ongoing turn highClock).mp holds.2
  · intro outside
    exact ⟨KRKHighClock.strong_hold material,
      (high_clock_hold_iff material ongoing turn highClock).mpr outside⟩

theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace)
 (win : F σ s) :
    (LastReply sk rs wk ∧ W σ 2 s ∧ ¬W σ 1 s) ∨
      (¬LastReply sk rs wk ∧ W σ 4 s ∧ ¬W σ 3 s) := by
  by_cases last : LastReply sk rs wk
  · have noClaim := weak_force_no_claim ongoing turn win
    exact Or.inl ⟨last, (rule_two_iff material ongoing turn).mpr ⟨last, noClaim⟩, weak_not_one ongoing turn⟩
  · have clear := (high_clock_force_iff material ongoing turn high).mp win
    refine Or.inr ⟨last, sufficient material ongoing turn clear, ?_⟩
    intro cert
    have board := raw_ruleMateWithin_project s σ 3 cert
    rcases (weak_three_iff material turn (admitted_far material)).mp board with mate | ready
    · exact mate.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
    · exact last ready

end EndgameChess.Rules.KRKGlobalWeakBand
