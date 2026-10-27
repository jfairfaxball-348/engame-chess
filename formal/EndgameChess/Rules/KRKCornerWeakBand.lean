import EndgameChess.Rules.KRKWeakBranch
import EndgameChess.Rules.KRKHighClock.StrongHold

namespace EndgameChess.Rules.KRKCornerWeakBand
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKWeakBranch RawHistoryLayer KRKHolding
set_option maxHeartbeats 400000

def east : Square := (1, 0)
def north : Square := (0, 1)
def inward : Square := (1, 1)

def Guard (sk rs wk t : Square) : Prop :=
  dInf wk t = 1 ∧ t ≠ rs ∧ 2 ≤ dInf sk t ∧ ¬RookSees rs t sk t

theorem guard_legal {q : Position} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (guard : Guard sk rs wk t) :
    isLegal q ⟨wk, t, none⟩ = true :=
  lone_step_legal material turn (StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2)

theorem step_guard {sk rs wk t : Square}
    (step : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩) : Guard sk rs wk t := by
  cases step with
  | lone distance notRook far notCheck => exact ⟨distance, notRook, far, notCheck⟩

theorem neighbour_cases {wk t : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (distance : dInf wk t = 1) : t = east ∨ t = north ∨ t = inward := by
  have coordinates : (t.1.val = 1 ∧ t.2.val = 0) ∨
      (t.1.val = 0 ∧ t.2.val = 1) ∨ (t.1.val = 1 ∧ t.2.val = 1) := by
    simp only [dInf, absDiff, file, rank] at distance
    omega
  rcases coordinates with e | n | d
  · left; rw [square_eq_iff]; exact e
  · right; left; rw [square_eq_iff]; exact n
  · right; right; rw [square_eq_iff]; exact d

def CornerClear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 99 ∧ RawRepetition.currentOccurrences s < 3 ∧
    ¬Guard sk rs wk inward ∧
    (Guard sk rs wk east → RawRepetition.occurrences s.trace (firstBoard s wk east) < 2 ∧
      KRKSlotPrefix.Horizontal.Clear s sk rs wk east) ∧
    (Guard sk rs wk north → RawRepetition.occurrences s.trace (firstBoard s wk north) < 2 ∧
      KRKSlotPrefix.Vertical.Clear s sk rs wk north)

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) (win : F σ s) :
    CornerClear s.val sk rs wk := by
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
  have noInward : ¬Guard sk rs wk inward := by
    intro guard
    have legal := guard_legal material turn guard
    have childWin := all (weakChild s ongoing wk inward legal) ⟨_, legal, rfl⟩
    have history := child_history_of_force material ongoing turn safe high legal childWin
    have depth := KRKFourPlyEscape.three_depth_zero (history_geometry history)
    have positive : KRKEdgeDepth.depth inward = 1 := by decide
    omega
  refine ⟨safe, time, claims.2.1, noInward, ?_, ?_⟩
  · intro guard
    have legal := guard_legal material turn guard
    have childWin := all (weakChild s ongoing wk east legal) ⟨_, legal, rfl⟩
    have history := child_history_of_force material ongoing turn safe high legal childWin
    exact ⟨(claims.2.2 _ legal).2,
      (KRKSlotPrefix.Horizontal.history_append_iff material turn safe legal rfl rfl).mp history⟩
  · intro guard
    have legal := guard_legal material turn guard
    have childWin := all (weakChild s ongoing wk north legal) ⟨_, legal, rfl⟩
    have history := child_history_of_force material ongoing turn safe high legal childWin
    exact ⟨(claims.2.2 _ legal).2,
      (KRKSlotPrefix.Vertical.history_append_iff material turn safe legal rfl rfl).mp history⟩

theorem sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (clear : CornerClear s.val sk rs wk) : W σ 4 s := by
  have safe := clear.1
  have time := clear.2.1
  have noInward := clear.2.2.2.1
  have eastClear := clear.2.2.2.2.1
  have northClear := clear.2.2.2.2.2
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
      rcases neighbour_cases file rank guard.1 with e | n | d
      · subst t; exact (eastClear guard).1
      · subst t; exact (northClear guard).1
      · subst t; exact False.elim (noInward guard)
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
  have guard := step_guard step
  rcases neighbour_cases file rank guard.1 with e | n | d
  · subst t
    have history := (KRKSlotPrefix.Horizontal.history_append_iff material turn safe childLegal rfl rfl).mpr (eastClear guard).2
    exact child_certificate material ongoing turn safe childLegal time (eastClear guard).1 history
  · subst t
    have history := (KRKSlotPrefix.Vertical.history_append_iff material turn safe childLegal rfl rfl).mpr (northClear guard).2
    exact child_certificate material ongoing turn safe childLegal time (northClear guard).1 history
  · subst t; exact False.elim (noInward guard)

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    F σ s ↔ CornerClear s.val sk rs wk := by
  constructor
  · exact necessary material ongoing turn high file rank
  · intro clear; exact ⟨4, sufficient material ongoing turn file rank clear⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    KRKWinning.ActualWin σ s ↔ CornerClear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn highClock file rank)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    RuleHold σ.opp s ↔ ¬CornerClear s.val sk rs wk := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn highClock file rank] using dual

/-- Both players can hold exactly on the complement of the evaluated
winning region in this band. -/
theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    (RuleHold σ s ∧ RuleHold σ.opp s) ↔ ¬CornerClear s.val sk rs wk := by
  constructor
  · intro holds
    exact (high_clock_hold_iff material ongoing turn highClock file rank).mp holds.2
  · intro outside
    exact ⟨KRKHighClock.strong_hold material,
      (high_clock_hold_iff material ongoing turn highClock file rank).mpr outside⟩

theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) (win : F σ s) :
    (LastReply sk rs wk ∧ W σ 2 s ∧ ¬W σ 1 s) ∨
      (¬LastReply sk rs wk ∧ W σ 4 s ∧ ¬W σ 3 s) := by
  by_cases last : LastReply sk rs wk
  · have noClaim := weak_force_no_claim ongoing turn win
    exact Or.inl ⟨last, (rule_two_iff material ongoing turn).mpr ⟨last, noClaim⟩, weak_not_one ongoing turn⟩
  · have clear := (high_clock_force_iff material ongoing turn high file rank).mp win
    refine Or.inr ⟨last, sufficient material ongoing turn file rank clear, ?_⟩
    intro cert
    have board := raw_ruleMateWithin_project s σ 3 cert
    rcases (weak_three_iff material turn (admitted_far material)).mp board with mate | ready
    · exact mate.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
    · exact last ready

end EndgameChess.Rules.KRKCornerWeakBand
