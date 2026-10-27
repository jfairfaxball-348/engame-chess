import EndgameChess.Rules.KRKSlotPrefix
import EndgameChess.Rules.KRKOppositionHistory

namespace EndgameChess.Rules.KRKWeakBranch
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory RawHistoryLayer KRKHolding
set_option maxHeartbeats 300000

theorem history_geometry {s : RawTrace.State} {sk rs wk : Square}
    (history : ThreeHistory s sk rs wk) : Three sk rs wk := by
  rcases history with immediate | ⟨t, _, distance, notRook, far, last, _⟩ |
    ⟨t, _, sees, notKing, notWeak, last, _⟩
  · exact Or.inl immediate
  · exact Or.inr (Or.inl ⟨t, distance, notRook, far, last⟩)
  · exact Or.inr (Or.inr ⟨t, sees, notKing, notWeak, last⟩)

theorem child_clock {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (safe : SafeRook sk rs wk)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true) :
    RawClock.clock (weakChild s ongoing wk t legal).val.trace = RawClock.clock s.val.trace + 1 := by
  have quiet := weak_safe_quiet material turn safe legal
  change (if RawClock.zeroing (erase s) ⟨wk, t, none⟩ then 0 else RawClock.clock s.val.trace + 1) = _
  simp only [quiet, Bool.false_eq_true, ↓reduceIte]

theorem child_ongoing_of_force {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (legal : isLegal (erase s) ⟨wk, t, none⟩ = true)
    (win : F σ (weakChild s ongoing wk t legal)) : Ongoing (weakChild s ongoing wk t legal) := by
  have nextTurn : (erase (weakChild s ongoing wk t legal)).turn = σ := by
    change (play (erase s) _).turn = σ
    simp [play_turn, turn, opp_opp]
  apply Classical.byContradiction
  intro stopped
  have goal := (KRKHighClock.terminal_force_iff_goal stopped).mp win
  exact opp_ne σ (nextTurn.symm.trans goal.1)

theorem child_history_of_force {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (safe : SafeRook sk rs wk)
    (high : 95 ≤ RawClock.clock s.val.trace) (legal : isLegal (erase s) ⟨wk, t, none⟩ = true)
    (win : F σ (weakChild s ongoing wk t legal)) :
    ThreeHistory (RawTrace.append s.val ⟨wk, t, none⟩ legal) sk rs t := by
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase (weakChild s ongoing wk t legal)).turn = σ := by
    change (play (erase s) _).turn = σ
    simp [play_turn, turn, opp_opp]
  have clock := child_clock material ongoing turn safe legal
  exact (KRKThreePly.high_clock_force_iff (s := weakChild s ongoing wk t legal) next
    (child_ongoing_of_force material ongoing turn legal win) nextTurn (by omega)).mp win

theorem child_certificate {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (safe : SafeRook sk rs wk)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true)
    (time : RawClock.clock s.val.trace < 99)
    (count : RawRepetition.occurrences s.val.trace (firstBoard s.val wk t) < 2)
    (history : ThreeHistory (RawTrace.append s.val ⟨wk, t, none⟩ legal) sk rs t) :
    W σ 3 (weakChild s ongoing wk t legal) := by
  let v := weakChild s ongoing wk t legal
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase v).turn = σ := by change (play (erase s) _).turn = σ; simp [play_turn, turn, opp_opp]
  obtain ⟨far, notCheck⟩ := krk_strong_arrival_geometry ⟨_, legal, rfl⟩ next nextTurn
  have board : MateWithin σ 3 (erase v) := (strong_three_iff next nextTurn far notCheck).mpr (history_geometry history)
  have nonempty : ∃ r, Legal (erase v) r := by
    apply Classical.byContradiction
    intro noMoves
    have goal := (forceMate_no_moves_iff noMoves).mp ⟨3, board⟩
    exact opp_ne σ (nextTurn.symm.trans goal.1)
  have clock := child_clock material ongoing turn safe legal
  change RawClock.clock v.val.trace = RawClock.clock s.val.trace + 1 at clock
  have current : RawRepetition.currentOccurrences v.val < 3 := by
    have update := RawRepetition.append_currentOccurrences s.val ⟨wk, t, none⟩ legal
    change RawRepetition.currentOccurrences v.val =
      RawRepetition.occurrences s.val.trace (firstBoard s.val wk t) + 1 at update
    omega
  have childOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨3, board⟩, nonempty, by omega, by omega⟩
  exact history_three_sufficient (s := v) next childOngoing nextTurn history

theorem admitted_far {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) : 2 ≤ dInf sk wk := by
  have arrival : ∃ p, Legal p (erase s) := by
    rcases s with ⟨⟨q, trace⟩, admitted⟩
    cases trace with
    | start => exact False.elim (initial_not_KRK σ sk rs wk material)
    | @snoc q prior m hm => exact ⟨q, m, hm, rfl⟩
  obtain ⟨p, legal⟩ := arrival
  exact KRKEdgeDepth.arrival_far legal material

theorem weak_not_one {s : State} {σ : Colour} (ongoing : Ongoing s)
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

end EndgameChess.Rules.KRKWeakBranch
