import EndgameChess.Rules.KRKSecondOppositionPrefix
import EndgameChess.Rules.KRKOppositionHistory

namespace EndgameChess.Rules.KRKSecondOppositionHistory
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKRookRayBarriers RawHistoryLayer KRKHolding
set_option maxHeartbeats 300000

def WestClear (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  RawRepetition.occurrences s.trace (firstBoard s wk t) < 2 ∧
    (OriginalRay s sk rs wk t (0 : Fin 8) ∨ (rs.1.val = 2 ∧ OriginalKing s sk wk t))

theorem west_necessary {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (tx : t.1.val = 1) (ty : t.2.val = 0)
    (noClaim : ¬CanClaim s) (all : ∀ v, BoardStep s v → F σ v)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true) :
    RawClock.clock s.val.trace < 97 ∧ WestClear s.val sk rs wk t := by
  let v := weakChild s ongoing wk t legal
  have edge : BoardStep s v := ⟨_, legal, rfl⟩
  have win := all v edge
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase v).turn = σ := by change (play (erase s) _).turn = σ; simp [play_turn, turn, opp_opp]
  have nextOngoing : Ongoing v := by
    apply Classical.byContradiction
    intro stopped
    have goal := (KRKHighClock.terminal_force_iff_goal stopped).mp win
    exact opp_ne σ (nextTurn.symm.trans goal.1)
  have clock : RawClock.clock v.val.trace = RawClock.clock s.val.trace + 1 := by
    have quiet := weak_safe_quiet material turn safe legal
    change (if RawClock.zeroing (erase s) ⟨wk, t, none⟩ then 0 else RawClock.clock s.val.trace + 1) = _
    simp only [quiet, Bool.false_eq_true, ↓reduceIte]
  have criterion := (KRKNearKingBarrier.high_clock_force_iff (s := v) next nextOngoing nextTurn
    (by omega) sx sy tx ty ry).mp win
  have original := (west_alternatives_append_iff material turn rank sx sy ry tx ty legal).mp criterion
  have claims := (RawClaims.no_threshold_iff s.val).mp noClaim
  exact ⟨original.1, (claims.2.2 _ legal).2, original.2⟩

theorem west_certificate {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (high : 95 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (tx : t.1.val = 1) (ty : t.2.val = 0)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true)
    (time : RawClock.clock s.val.trace < 97) (clear : WestClear s.val sk rs wk t) :
    W σ 3 (weakChild s ongoing wk t legal) := by
  let v := weakChild s ongoing wk t legal
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase v).turn = σ := by change (play (erase s) _).turn = σ; simp [play_turn, turn, opp_opp]
  obtain ⟨far, notCheck⟩ := krk_strong_arrival_geometry ⟨_, legal, rfl⟩ next nextTurn
  have three : Three sk rs t := by
    apply (three_near_iff material.1 tx ty).mpr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sx, sy, Or.inr (Or.inl ry)⟩))))
  have board : MateWithin σ 3 (erase v) := (strong_three_iff next nextTurn far notCheck).mpr three
  have nonempty : ∃ r, Legal (erase v) r := by
    apply Classical.byContradiction
    intro noMoves
    have goal := (forceMate_no_moves_iff noMoves).mp ⟨3, board⟩
    exact opp_ne σ (nextTurn.symm.trans goal.1)
  have clock : RawClock.clock v.val.trace = RawClock.clock s.val.trace + 1 := by
    have quiet := weak_safe_quiet material turn safe legal
    change (if RawClock.zeroing (erase s) ⟨wk, t, none⟩ then 0 else RawClock.clock s.val.trace + 1) = _
    simp only [quiet, Bool.false_eq_true, ↓reduceIte]
  have count : RawRepetition.currentOccurrences v.val < 3 := by
    have update := RawRepetition.append_currentOccurrences s.val ⟨wk, t, none⟩ legal
    change RawRepetition.currentOccurrences v.val =
      RawRepetition.occurrences s.val.trace (firstBoard s.val wk t) + 1 at update
    have bound := clear.1
    omega
  have nextOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨3, board⟩, nonempty, by omega, by omega⟩
  have criterion := (west_alternatives_append_iff material turn rank sx sy ry tx ty legal).mpr ⟨time, clear.2⟩
  have win := (KRKNearKingBarrier.high_clock_force_iff (s := v) next nextOngoing nextTurn
    (by omega) sx sy tx ty ry).mpr criterion
  exact (KRKNearKingBarrier.high_clock_exact_three (s := v) next nextOngoing nextTurn (by omega) sx tx ty).1.mp win

end EndgameChess.Rules.KRKSecondOppositionHistory
