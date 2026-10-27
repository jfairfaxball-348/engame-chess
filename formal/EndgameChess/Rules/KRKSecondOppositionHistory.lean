import EndgameChess.Rules.KRKSecondWestHistory

namespace EndgameChess.Rules.KRKSecondOppositionHistory
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKRookRayBarriers RawHistoryLayer KRKHolding
set_option maxHeartbeats 300000

def SecondClear (s : RawTrace.State) (sk rs wk : Square) (high : wk.1.val ≤ 4) : Prop :=
  RawClock.clock s.trace < 97 ∧ RawRepetition.currentOccurrences s < 3 ∧
    (rs.1.val + 1 ≠ wk.1.val → WestClear s sk rs wk (west wk)) ∧
    (rs.1.val ≠ wk.1.val + 1 → BranchClear s sk rs wk (east wk high) (eastFile wk high))

theorem second_necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (limit : wk.1.val ≤ 4)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) (win : F σ s) :
    SecondClear s.val sk rs wk limit := by
  obtain ⟨noClaim, _, all⟩ := weak_force_data ongoing turn win
  have leftBranch : rs.1.val + 1 ≠ wk.1.val →
      RawClock.clock s.val.trace < 97 ∧ WestClear s.val sk rs wk (west wk) := by
    intro guard
    apply west_necessary material ongoing turn highClock rank sx sy ry
      (by dsimp [west]; omega) rfl noClaim all
      (west_legal material turn rank (by omega) limit (by omega) sy ry guard)
  have rightBranch : rs.1.val ≠ wk.1.val + 1 →
      RawClock.clock s.val.trace < 97 ∧ BranchClear s.val sk rs wk (east wk limit) (eastFile wk limit) := by
    intro guard
    apply branch_necessary material ongoing turn highClock rank sy ry rfl
      (by dsimp [east]; omega) (by dsimp [east]; omega) ?_ noClaim all
      (east_legal material turn rank (by omega) limit (by omega) sy ry guard)
    unfold Side; right; dsimp [east, eastFile]; omega
  have time : RawClock.clock s.val.trace < 97 := by
    by_cases guard : rs.1.val + 1 ≠ wk.1.val
    · exact (leftBranch guard).1
    · exact (rightBranch (by omega)).1
  exact ⟨time, (RawClaims.no_threshold_iff s.val).mp noClaim |>.2.1,
    fun guard => (leftBranch guard).2, fun guard => (rightBranch guard).2⟩

theorem second_sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (limit : wk.1.val ≤ 4)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (clear : SecondClear s.val sk rs wk limit) : W σ 4 s := by
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have noClaim : ¬CanClaim s := by
    apply (RawClaims.no_threshold_iff s.val).mpr
    refine ⟨by have time := clear.1; omega, clear.2.1, ?_⟩
    intro m legal
    obtain ⟨t, next, step⟩ := krk_safe_reply material turn safe ⟨m, legal, rfl⟩
    have canonical := weak_move_eq material turn legal next.1
    constructor
    · have bound := RawClock.append_clock_le s.val m legal
      have time := clear.1
      omega
    · rw [canonical]
      rcases opposition_step_cases rank (by omega) limit (by omega) sy ry step with ⟨target, guard⟩ | ⟨target, guard⟩
      · subst t; exact (clear.2.2.1 guard).1
      · subst t; exact (clear.2.2.2 guard).1
  have nonempty : ∃ v, BoardStep s v := by
    by_cases guard : rs.1.val + 1 ≠ wk.1.val
    · have legal := west_legal material turn rank (by omega) limit (by omega) sy ry guard
      exact ⟨weakChild s ongoing wk (west wk) legal, ⟨_, legal, rfl⟩⟩
    · have legal := east_legal material turn rank (by omega) limit (by omega) sy ry (by omega)
      exact ⟨weakChild s ongoing wk (east wk limit) legal, ⟨_, legal, rfl⟩⟩
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
  rcases opposition_step_cases rank (by omega) limit (by omega) sy ry step with ⟨target, guard⟩ | ⟨target, guard⟩
  · subst t
    exact west_certificate material ongoing turn highClock rank sx sy ry (by dsimp [west]; omega) rfl
      childLegal clear.1 (clear.2.2.1 guard)
  · subst t
    apply branch_certificate material ongoing turn highClock rank sy ry rfl
      (by dsimp [east]; omega) (by dsimp [east]; omega) ?_ childLegal clear.1 (clear.2.2.2 guard)
    unfold Side; right; dsimp [east, eastFile]; omega

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (limit : wk.1.val ≤ 4)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    F σ s ↔ SecondClear s.val sk rs wk limit := by
  constructor
  · exact second_necessary material ongoing turn highClock rank file limit sx sy ry
  · intro clear
    exact ⟨4, second_sufficient material ongoing turn highClock rank file limit sx sy ry clear⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (limit : wk.1.val ≤ 4)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    KRKWinning.ActualWin σ s ↔ SecondClear s.val sk rs wk limit :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn highClock rank file limit sx sy ry)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (limit : wk.1.val ≤ 4)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    RuleHold σ.opp s ↔ ¬SecondClear s.val sk rs wk limit := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn highClock rank file limit sx sy ry] using dual

theorem high_clock_exact_four {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (file : wk.1.val = 2) (limit : wk.1.val ≤ 4)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    (F σ s ↔ W σ 4 s) ∧ ¬W σ 3 s := by
  constructor
  · constructor
    · intro win
      exact second_sufficient material ongoing turn highClock rank file limit sx sy ry
        (second_necessary material ongoing turn highClock rank file limit sx sy ry win)
    · intro win; exact ⟨4, win⟩
  · intro cert
    have far : 2 ≤ dInf sk wk := by simp [dInf, absDiff, sy, rank] <;> omega
    have board := raw_ruleMateWithin_project s σ 3 cert
    rcases (weak_three_iff material turn far).mp board with mate | last
    · exact mate.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
    · obtain ⟨_, _, sides⟩ := (last_middle_iff rank (by omega) (by omega)).mp last
      omega

end EndgameChess.Rules.KRKSecondOppositionHistory
