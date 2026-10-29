import EndgameChess.Rules.KRKNinePlyExact
import EndgameChess.Rules.KRKSixPlyExact
import EndgameChess.Rules.KRKFourPlyExact

namespace EndgameChess.Rules.KRKTenPlyHistory
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKWeakBranch RawHistoryLayer KRKHolding
open KRKCornerWeakBand (Guard guard_legal step_guard)
set_option maxHeartbeats 500000

def AfterWeak (s : RawTrace.State) (initial destination sk rs wk : Square) : Prop :=
  ∀ legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true,
    KRKNinePlyHistory.Clear (RawTrace.append s ⟨initial,destination,none⟩ legal) sk rs wk

theorem after_weak_iff {s : RawTrace.State} {σ : Colour} {sk rs initial destination : Square}
    (_material : IsKRK (RawTrace.erase s) σ sk rs initial) (_turn : (RawTrace.erase s).turn = σ.opp)
    (_safe : SafeRook sk rs initial) (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) :
    KRKNinePlyHistory.Clear (RawTrace.append s ⟨initial,destination,none⟩ legal) sk rs destination ↔
      AfterWeak s initial destination sk rs destination := ⟨fun h _ => h,fun h => h legal⟩

theorem child_nine_certificate {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (safe : SafeRook sk rs wk)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true)
    (time : RawClock.clock s.val.trace < 99)
    (count : RawRepetition.occurrences s.val.trace (firstBoard s.val wk t) < 2)
    (history : KRKNinePlyHistory.Clear (RawTrace.append s.val ⟨wk, t, none⟩ legal) sk rs t) :
    W σ 9 (weakChild s ongoing wk t legal) := by
  let v := weakChild s ongoing wk t legal
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase v).turn = σ := by change (play (erase s) _).turn = σ; simp [play_turn, turn, opp_opp]
  obtain ⟨far, notCheck⟩ := krk_strong_arrival_geometry ⟨_, legal, rfl⟩ next nextTurn
  have board : MateWithin σ 9 (erase v) := KRKNinePlyHistory.clear_kernel next nextTurn far notCheck history
  have nonempty : ∃ r, Legal (erase v) r := by
    apply Classical.byContradiction
    intro noMoves
    have goal := (forceMate_no_moves_iff noMoves).mp ⟨9, board⟩
    exact opp_ne σ (nextTurn.symm.trans goal.1)
  have clock := child_clock material ongoing turn safe legal
  change RawClock.clock v.val.trace = RawClock.clock s.val.trace + 1 at clock
  have current : RawRepetition.currentOccurrences v.val < 3 := by
    have update := RawRepetition.append_currentOccurrences s.val ⟨wk, t, none⟩ legal
    change RawRepetition.currentOccurrences v.val =
      RawRepetition.occurrences s.val.trace (firstBoard s.val wk t) + 1 at update
    omega
  have childOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨9, board⟩, nonempty, by omega, by omega⟩
  exact KRKNinePlyHistory.sufficient (s := v) next childOngoing nextTurn history

def Clear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 99 ∧ RawRepetition.currentOccurrences s < 3 ∧
    ∀ t : Square, Guard sk rs wk t →
      RawRepetition.occurrences s.trace (firstBoard s wk t) < 2 ∧
        AfterWeak s wk t sk rs t

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 89 ≤ RawClock.clock s.val.trace) (win : F σ s) :
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
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase (weakChild s ongoing wk t legal)).turn = σ := by
    change (play (erase s) _).turn = σ; simp only [play_turn,turn,opp_opp]
  have childClock := child_clock material ongoing turn safe legal
  have evaluated := (KRKNinePlyHistory.high_clock_force_iff (s := weakChild s ongoing wk t legal)
    next (child_ongoing_of_force material ongoing turn legal childWin) nextTurn (by omega)).mp childWin
  exact ⟨(claims.2.2 _ legal).2,(after_weak_iff material turn safe legal).mp evaluated⟩

theorem sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (clear : Clear s.val sk rs wk) : W σ 10 s := by
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
  have history := (after_weak_iff material turn safe childLegal).mpr branch.2
  exact child_nine_certificate material ongoing turn safe childLegal time branch.1 history

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 89 ≤ RawClock.clock s.val.trace) :
    F σ s ↔ Clear s.val sk rs wk := by
  constructor
  · exact necessary material ongoing turn high
  · intro clear; exact ⟨10, sufficient material ongoing turn clear⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 89 ≤ RawClock.clock s.val.trace)
 :
    KRKWinning.ActualWin σ s ↔ Clear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn highClock)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 89 ≤ RawClock.clock s.val.trace)
 :
    RuleHold σ.opp s ↔ ¬Clear s.val sk rs wk := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn highClock] using dual

/-- Both players can hold exactly on the complement of the evaluated
winning region in this band. -/
theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 89 ≤ RawClock.clock s.val.trace)
 :
    (RuleHold σ s ∧ RuleHold σ.opp s) ↔ ¬Clear s.val sk rs wk := by
  constructor
  · intro holds
    exact (high_clock_hold_iff material ongoing turn highClock).mp holds.2
  · intro outside
    exact ⟨KRKHighClock.strong_hold material,
      (high_clock_hold_iff material ongoing turn highClock).mpr outside⟩


end EndgameChess.Rules.KRKTenPlyHistory
