import EndgameChess.Rules.KRKOppositionPrefix
import EndgameChess.Rules.RawClock.StepBound

namespace EndgameChess.Rules.KRKOppositionHistory
open EndgameChess.KK KRKLastReply KRKThreePly KRKRookRayBarriers RawHistoryLayer KRKHolding

def west (wk : Square) : Square :=
  (⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩, 0)

def east (wk : Square) (high : wk.1.val ≤ 4) : Square :=
  (⟨wk.1.val + 1, by omega⟩, 0)

def westFile (wk : Square) : Fin 8 :=
  ⟨wk.1.val - 2, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩

def eastFile (wk : Square) (high : wk.1.val ≤ 4) : Fin 8 := ⟨wk.1.val + 2, by omega⟩

def BranchClear (s : RawTrace.State) (sk rs wk t : Square) (f : Fin 8) : Prop :=
  RawRepetition.occurrences s.trace (firstBoard s wk t) < 2 ∧ OriginalRay s sk rs wk t f

/-- Two independent rank intervals, one per actual weak reply. All three
key queries per branch use the same original incoming trace. -/
def OppositionClear (s : RawTrace.State) (sk rs wk : Square) (high : wk.1.val ≤ 4) : Prop :=
  RawClock.clock s.trace < 97 ∧ RawRepetition.currentOccurrences s < 3 ∧
    (rs.1.val + 1 ≠ wk.1.val → BranchClear s sk rs wk (west wk) (westFile wk)) ∧
    (rs.1.val ≠ wk.1.val + 1 → BranchClear s sk rs wk (east wk high) (eastFile wk high))

theorem opposition_step_cases {sk rs wk u : Square} (rank : wk.2.val = 0)
    (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (step : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩) :
    (u = west wk ∧ rs.1.val + 1 ≠ wk.1.val) ∨
    (u = east wk high ∧ rs.1.val ≠ wk.1.val + 1) := by
  cases step with
  | lone distance _ far notCheck =>
    have near := distance
    simp only [dInf, absDiff, rank, sx, sy] at near far
    have uy : u.2.val = 0 := by omega
    have ux : u.1.val + 1 = wk.1.val ∨ u.1.val = wk.1.val + 1 := by omega
    rcases ux with left | right
    · left
      refine ⟨?_, ?_⟩
      · rw [square_eq_iff]; dsimp [west]; omega
      · intro rookFile
        apply notCheck
        simp only [RookSees, RookLine, OnSeg]
        omega
    · right
      refine ⟨?_, ?_⟩
      · rw [square_eq_iff]; dsimp [east]; omega
      · intro rookFile
        apply notCheck
        simp only [RookSees, RookLine, OnSeg]
        omega

theorem west_legal {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (guard : rs.1.val + 1 ≠ wk.1.val) : isLegal q ⟨wk, west wk, none⟩ = true := by
  apply lone_step_legal material turn
  refine StepM.lone ?_ ?_ ?_ ?_
  · simp [dInf, absDiff, west, rank] <;> omega
  · rw [ne_iff_coords]; dsimp [west]; omega
  · simp [dInf, absDiff, west, sx, sy] <;> omega
  · simp [RookSees, RookLine, west]; omega

theorem east_legal {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (guard : rs.1.val ≠ wk.1.val + 1) : isLegal q ⟨wk, east wk high, none⟩ = true := by
  apply lone_step_legal material turn
  refine StepM.lone ?_ ?_ ?_ ?_
  · simp [dInf, absDiff, east, rank] <;> omega
  · rw [ne_iff_coords]; dsimp [east]; omega
  · simp [dInf, absDiff, east, sx, sy] <;> omega
  · simp [RookSees, RookLine, east]; omega

private theorem weak_force_data {s : State} {σ : Colour} (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (win : F σ s) :
    ¬CanClaim s ∧ (∃ v, BoardStep s v) ∧ ∀ v, BoardStep s v → F σ v := by
  have notGoal : ¬G σ s := fun goal =>
    goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
  obtain ⟨n, cert⟩ := win
  cases n with
  | zero => exact False.elim (notGoal cert)
  | succ n =>
    rcases cert with goal | ⟨_, chosen | defended⟩
    · exact False.elim (notGoal goal)
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · exact ⟨defended.2.1, defended.2.2.1, fun v edge => ⟨n, defended.2.2.2 v edge⟩⟩

theorem weak_force_no_claim {s : State} {σ : Colour} (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (win : F σ s) : ¬CanClaim s :=
  (weak_force_data ongoing turn win).1

private theorem branch_necessary {s : State} {σ : Colour} {sk rs wk t : Square} {f : Fin 8}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (trank : t.2.val = 0) (low : 2 ≤ t.1.val) (high : t.1.val ≤ 5) (side : Side sk t f)
    (noClaim : ¬CanClaim s) (all : ∀ v, BoardStep s v → F σ v)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true) :
    RawClock.clock s.val.trace < 97 ∧ BranchClear s.val sk rs wk t f := by
  let v : State := ⟨RawTrace.append s.val ⟨wk, t, none⟩ legal,
    ((StoppedHistory.append_and_reply_lifting s.val).1 _ legal).mpr ⟨s.property, ongoing⟩⟩
  have edge : BoardStep s v := ⟨_, legal, rfl⟩
  have childWin := all v edge
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase v).turn = σ := by change (play (erase s) _).turn = σ; simp [play_turn, turn, opp_opp]
  have nextOngoing : Ongoing v := by
    apply Classical.byContradiction
    intro stopped
    have goal := (KRKHighClock.terminal_force_iff_goal stopped).mp childWin
    exact opp_ne σ (nextTurn.symm.trans goal.1)
  have quiet := weak_safe_quiet material turn safe legal
  have clock : RawClock.clock v.val.trace = RawClock.clock s.val.trace + 1 := by
    change (if RawClock.zeroing (erase s) ⟨wk, t, none⟩ then 0 else RawClock.clock s.val.trace + 1) = _
    simp only [quiet, Bool.false_eq_true, ↓reduceIte]
  have ray := (KRKRookRayBarriers.high_clock_force_iff (s := v) next nextOngoing nextTurn
    (by omega) trank low high sy ry side).mp childWin
  have original := (ray_append_iff material turn rank sy ry trank low high side legal).mp ray
  have claims := (RawClaims.no_threshold_iff s.val).mp noClaim
  exact ⟨original.1, (claims.2.2 _ legal).2, original.2⟩

theorem opposition_necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) (win : F σ s) :
    OppositionClear s.val sk rs wk high := by
  obtain ⟨noClaim, _, all⟩ := weak_force_data ongoing turn win
  have leftBranch : rs.1.val + 1 ≠ wk.1.val →
      RawClock.clock s.val.trace < 97 ∧ BranchClear s.val sk rs wk (west wk) (westFile wk) := by
    intro guard
    apply branch_necessary material ongoing turn highClock rank sy ry rfl
      (by dsimp [west]; omega) (by dsimp [west]; omega) ?_ noClaim all
      (west_legal material turn rank low high sx sy ry guard)
    unfold Side; left; dsimp [west, westFile]; omega
  have rightBranch : rs.1.val ≠ wk.1.val + 1 →
      RawClock.clock s.val.trace < 97 ∧ BranchClear s.val sk rs wk (east wk high) (eastFile wk high) := by
    intro guard
    apply branch_necessary material ongoing turn highClock rank sy ry rfl
      (by dsimp [east]; omega) (by dsimp [east]; omega) ?_ noClaim all
      (east_legal material turn rank low high sx sy ry guard)
    unfold Side; right; dsimp [east, eastFile]; omega
  have clock : RawClock.clock s.val.trace < 97 := by
    by_cases guard : rs.1.val + 1 ≠ wk.1.val
    · exact (leftBranch guard).1
    · exact (rightBranch (by omega)).1
  exact ⟨clock, ((RawClaims.no_threshold_iff s.val).mp noClaim).2.1,
    fun guard => (leftBranch guard).2, fun guard => (rightBranch guard).2⟩

private def weakChild (s : State) (ongoing : Ongoing s) (wk t : Square)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true) : State :=
  ⟨RawTrace.append s.val ⟨wk, t, none⟩ legal,
    ((StoppedHistory.append_and_reply_lifting s.val).1 _ legal).mpr ⟨s.property, ongoing⟩⟩

private theorem branch_certificate {s : State} {σ : Colour} {sk rs wk t : Square} {f : Fin 8}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (trank : t.2.val = 0) (low : 2 ≤ t.1.val) (high : t.1.val ≤ 5) (side : Side sk t f)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true)
    (clock : RawClock.clock s.val.trace < 97) (clear : BranchClear s.val sk rs wk t f) :
    W σ 3 (weakChild s ongoing wk t legal) := by
  let v := weakChild s ongoing wk t legal
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase v).turn = σ := by change (play (erase s) _).turn = σ; simp [play_turn, turn, opp_opp]
  have childClock : RawClock.clock v.val.trace = RawClock.clock s.val.trace + 1 := by
    have quiet := weak_safe_quiet material turn safe legal
    change (if RawClock.zeroing (erase s) ⟨wk, t, none⟩ then 0 else RawClock.clock s.val.trace + 1) = _
    simp only [quiet, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨y, allowed, _, _⟩ := clear.2
  have last := (ray_last_iff trank low high sy side).mpr allowed.1
  have sees := (ray_sees_iff trank sy ry side allowed.1).mpr allowed
  have notKing : (f, y) ≠ sk := by rw [ne_iff_coords]; dsimp only; unfold Side at side; omega
  have notWeak : (f, y) ≠ t := by
    have height := allowed.1
    rw [ne_iff_coords]; dsimp only; omega
  obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry ⟨_, legal, rfl⟩ next nextTurn
  have rookLegal := rook_entry_legal next nextTurn nextFar sees notKing notWeak last
  have board : MateWithin σ 3 (erase v) :=
    (strong_three_iff next nextTurn nextFar notCheck).mpr (Or.inr (Or.inr ⟨_, sees, notKing, notWeak, last⟩))
  have childCount : RawRepetition.currentOccurrences v.val < 3 := by
    have update := RawRepetition.append_currentOccurrences s.val ⟨wk, t, none⟩ legal
    change RawRepetition.currentOccurrences v.val =
      RawRepetition.occurrences s.val.trace (firstBoard s.val wk t) + 1 at update
    have count := clear.1
    omega
  have childOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨3, board⟩, ⟨_, ⟨_, rookLegal, rfl⟩⟩, by omega, by omega⟩
  have ray : ClearRay v.val sk rs t f :=
    (ray_append_iff material turn rank sy ry trank low high side legal).mpr ⟨clock, clear.2⟩
  have win := (KRKRookRayBarriers.high_clock_force_iff (s := v) next childOngoing nextTurn
    (by omega) trank low high sy ry side).mpr ray
  exact (KRKRookRayBarriers.high_clock_exact_three (s := v) next childOngoing nextTurn
    (by omega) trank low high side).1.mp win

private theorem move_branch {s : State} {σ : Colour} {sk rs wk : Square} {m : Move}
    (material : IsKRK (erase s) σ sk rs wk) (turn : (erase s).turn = σ.opp)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (clear : OppositionClear s.val sk rs wk high) (legal : isLegal (erase s) m = true) :
    ∃ t f, m = ⟨wk, t, none⟩ ∧ t.2.val = 0 ∧ 2 ≤ t.1.val ∧ t.1.val ≤ 5 ∧
      Side sk t f ∧ BranchClear s.val sk rs wk t f := by
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  obtain ⟨t, next, step⟩ := krk_safe_reply material turn safe ⟨m, legal, rfl⟩
  have canonical := weak_move_eq material turn legal next.1
  rcases opposition_step_cases rank low high sx sy ry step with ⟨target, guard⟩ | ⟨target, guard⟩
  · subst t
    refine ⟨west wk, westFile wk, canonical, rfl, ?_, ?_, ?_, clear.2.2.1 guard⟩
    · dsimp [west]; omega
    · dsimp [west]; omega
    · unfold Side; left; dsimp [west, westFile]; omega
  · subst t
    refine ⟨east wk high, eastFile wk high, canonical, rfl, ?_, ?_, ?_, clear.2.2.2 guard⟩
    · dsimp [east]; omega
    · dsimp [east]; omega
    · unfold Side; right; dsimp [east, eastFile]; omega

/-- Sufficiency on the original incoming trace. The attacker can choose
different good rook ranks after the two different weak replies. -/
theorem opposition_sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (clear : OppositionClear s.val sk rs wk high) : W σ 4 s := by
  have noClaim : ¬CanClaim s := by
    apply (RawClaims.no_threshold_iff s.val).mpr
    refine ⟨by have time := clear.1; omega, clear.2.1, ?_⟩
    intro m legal
    obtain ⟨t, f, canonical, _, _, _, _, branch⟩ := move_branch material turn rank low high sx sy ry clear legal
    constructor
    · have bound := RawClock.append_clock_le s.val m legal
      have time := clear.1
      omega
    · rw [canonical]
      exact branch.1
  have nonempty : ∃ v, BoardStep s v := by
    by_cases guard : rs.1.val + 1 ≠ wk.1.val
    · have legal := west_legal material turn rank low high sx sy ry guard
      exact ⟨weakChild s ongoing wk (west wk) legal, ⟨_, legal, rfl⟩⟩
    · have legal := east_legal material turn rank low high sx sy ry (by omega)
      exact ⟨weakChild s ongoing wk (east wk high) legal, ⟨_, legal, rfl⟩⟩
  refine Or.inr ⟨ongoing, Or.inr ⟨turn, noClaim, nonempty, ?_⟩⟩
  intro v edge
  obtain ⟨m, legal, rawEq⟩ := edge
  obtain ⟨t, f, canonical, trank, tlow, thigh, side, branch⟩ :=
    move_branch material turn rank low high sx sy ry clear legal
  subst m
  have cert := branch_certificate material ongoing turn highClock rank sy ry trank tlow thigh side legal clear.1 branch
  have equal : v = weakChild s ongoing wk t legal := Subtype.ext rawEq
  rwa [equal]

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    F σ s ↔ OppositionClear s.val sk rs wk high := by
  constructor
  · exact opposition_necessary material ongoing turn highClock rank low high sx sy ry
  · intro clear
    exact ⟨4, opposition_sufficient material ongoing turn highClock rank low high sx sy ry clear⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    KRKWinning.ActualWin σ s ↔ OppositionClear s.val sk rs wk high :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn highClock rank low high sx sy ry)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    RuleHold σ.opp s ↔ ¬OppositionClear s.val sk rs wk high := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn highClock rank low high sx sy ry] using dual

theorem high_clock_exact_four {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (highClock : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (sx : sk.1.val = wk.1.val) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) :
    (F σ s ↔ W σ 4 s) ∧ ¬W σ 3 s := by
  constructor
  · constructor
    · intro win
      exact opposition_sufficient material ongoing turn highClock rank low high sx sy ry
        (opposition_necessary material ongoing turn highClock rank low high sx sy ry win)
    · intro win; exact ⟨4, win⟩
  · intro cert
    have far : 2 ≤ dInf sk wk := by simp [dInf, absDiff, sy, rank] <;> omega
    have board := raw_ruleMateWithin_project s σ 3 cert
    rcases (weak_three_iff material turn far).mp board with mate | last
    · exact mate.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
    · obtain ⟨_, _, sides⟩ := (last_middle_iff rank (by omega) (by omega)).mp last
      omega

end EndgameChess.Rules.KRKOppositionHistory
