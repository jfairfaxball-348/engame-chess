import EndgameChess.Rules.KRKThreePly

namespace EndgameChess.Rules.KRKThreePly
open EndgameChess.KK RawHistoryLayer KRKLastReply KRKMateGeometry KRKImmediate
open KRKHighClock KRKWinning KRKHolding

private theorem strong_quiet {q : Position} {σ : Colour} {sk rs wk : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) : RawClock.zeroing q m = false := by
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal; exact legal.1
  obtain ⟨noPawn, targets⟩ := krk_material_targets material pseudo
  have empty : q.board m.dst = none := by
    cases atDst : q.board m.dst with
    | none => rfl
    | some piece => exact False.elim ((targets piece atDst).2.2 turn)
  have pawnFalse : (q.board m.src == some ⟨q.turn, .pawn⟩) = false := by
    rw [Bool.eq_false_iff]; simpa using noPawn
  simp [RawClock.zeroing, pawnFalse, empty]

/-- Two original-history barrier queries for a nonmating first move and its
forced weak reply. Both are measured before either move is appended. -/
def EntryClear (s : RawTrace.State) (m : Move) (wk u : Square) : Prop :=
  RawClock.clock s.trace < 98 ∧
    RawRepetition.occurrences s.trace (play (RawTrace.erase s) m) < 2 ∧
    RawRepetition.occurrences s.trace
      (play (play (RawTrace.erase s) m) ⟨wk, u, none⟩) < 2

/-- Evaluate all claims at the new weak-turn state in the original trace. -/
theorem entry_no_claim_iff {s : RawTrace.State} {σ : Colour}
    {sk rs wk ns nr u : Square} {m : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ)
    (legal : isLegal (RawTrace.erase s) m = true)
    (next : IsKRK (play (RawTrace.erase s) m) σ ns nr wk)
    (last : LastReply ns nr wk)
    (reply : isLegal (play (RawTrace.erase s) m) ⟨wk, u, none⟩ = true) :
    ¬RawClaims.AvailableThreshold (RawTrace.append s m legal) ↔ EntryClear s m wk u := by
  classical
  have nextTurn : (play (RawTrace.erase s) m).turn = σ.opp := by rw [play_turn, turn]
  have far := KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next
  have criterion := no_claim_at_unique_reply (s := RawTrace.append s m legal)
    next nextTurn far last reply
  have quiet := strong_quiet material turn legal
  have clock : RawClock.clock (RawTrace.append s m legal).trace = RawClock.clock s.trace + 1 := by
    rw [RawClock.append_clock, quiet]
    rfl
  have different : RawRepetition.key (play (RawTrace.erase s) m) ≠
      RawRepetition.key (play (play (RawTrace.erase s) m) ⟨wk, u, none⟩) := by
    intro same
    have sameTurn := congrArg Position.turn same
    change (play (RawTrace.erase s) m).turn =
      (play (play (RawTrace.erase s) m) ⟨wk, u, none⟩).turn at sameTurn
    simp only [play_turn, turn, opp_opp] at sameTurn
    exact opp_ne σ sameTurn.symm
  have query : RawRepetition.occurrences (RawTrace.append s m legal).trace
      (play (play (RawTrace.erase s) m) ⟨wk, u, none⟩) =
      RawRepetition.occurrences s.trace
        (play (play (RawTrace.erase s) m) ⟨wk, u, none⟩) := by
    unfold RawRepetition.occurrences
    rw [RawOccurrences.append_occurrences]
    simp only [different, ↓reduceIte, Nat.add_zero]
  rw [criterion, clock, RawRepetition.append_currentOccurrences]
  change (RawClock.clock s.trace + 1 < 99 ∧
    RawRepetition.occurrences s.trace (play (RawTrace.erase s) m) + 1 < 3 ∧
    RawRepetition.occurrences (RawTrace.append s m legal).trace
      (play (play (RawTrace.erase s) m) ⟨wk, u, none⟩) < 2) ↔ EntryClear s m wk u
  rw [query]
  unfold EntryClear
  omega

def KingHistoryEntry (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  ∃ t u, dInf sk t = 1 ∧ t ≠ rs ∧ 2 ≤ dInf t wk ∧ LastReply t rs wk ∧
    isLegal (RawTrace.erase s) ⟨sk, t, none⟩ = true ∧
    isLegal (play (RawTrace.erase s) ⟨sk, t, none⟩) ⟨wk, u, none⟩ = true ∧
    EntryClear s ⟨sk, t, none⟩ wk u

def RookHistoryEntry (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  ∃ t u, RookSees rs t sk wk ∧ t ≠ sk ∧ t ≠ wk ∧ LastReply sk t wk ∧
    isLegal (RawTrace.erase s) ⟨rs, t, none⟩ = true ∧
    isLegal (play (RawTrace.erase s) ⟨rs, t, none⟩) ⟨wk, u, none⟩ = true ∧
    EntryClear s ⟨rs, t, none⟩ wk u

def ThreeHistory (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  MateNow sk rs wk ∨ KingHistoryEntry s sk rs wk ∨ RookHistoryEntry s sk rs wk

private theorem canonical_king_material {q : Position} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (distance : dInf sk t = 1) (notRook : t ≠ rs) (far : 2 ≤ dInf t wk) :
    IsKRK (play q ⟨sk, t, none⟩) σ t rs wk := by
  have notOld : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have notWeak : t ≠ wk := ne_of_dInf_pos (by omega)
  have atKing : q.board sk = some ⟨q.turn, .king⟩ := by
    rw [turn, material.2.2.2]; exact krkBoard_sk
  have board := play_board_simple (m := ⟨sk, t, none⟩) atKing (by decide) rfl (fun _ => distance)
  refine ⟨notRook, notWeak, material.2.2.1, ?_⟩
  rw [board]; funext x; rw [material.2.2.2, turn]; unfold krkBoard
  by_cases e1 : x = t
  · subst x; simp
  · by_cases e2 : x = sk
    · subst x; simp [e1, material.1, material.2.1]
    · simp [e1, e2]

private theorem clear_entry_wins {s : State} {σ : Colour} {sk rs wk ns nr u : Square}
    {m : Move} (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (legal : isLegal (erase s) m = true)
    (next : IsKRK (play (erase s) m) σ ns nr wk) (last : LastReply ns nr wk)
    (reply : isLegal (play (erase s) m) ⟨wk, u, none⟩ = true)
    (clear : EntryClear s.val m wk u) : W σ 3 s := by
  let v : State := ⟨RawTrace.append s.val m legal,
    ((StoppedHistory.append_and_reply_lifting s.val).1 m legal).mpr ⟨s.property, ongoing⟩⟩
  have nextTurn : (erase v).turn = σ.opp := by change (play (erase s) m).turn = σ.opp; rw [play_turn, turn]
  have nextFar := KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next
  have board : MateWithin σ 2 (erase v) := (weak_two_iff next nextTurn nextFar).mpr (Or.inr last)
  have noClaim : ¬CanClaim v := (entry_no_claim_iff material turn legal next last reply).mpr clear
  have bounds := (RawClaims.no_threshold_iff v.val).mp noClaim
  have childOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨2, board⟩, ⟨_, ⟨⟨wk, u, none⟩, reply, rfl⟩⟩,
      by have h := bounds.1; omega, by have h := bounds.2.1; omega⟩
  have child := (rule_two_iff (s := v) next childOngoing nextTurn).mpr ⟨last, noClaim⟩
  exact Or.inr ⟨ongoing, Or.inl ⟨turn, v, ⟨m, legal, rfl⟩, child⟩⟩

/-- Sufficiency of the explicit coordinate and two-key barrier formula, at
any clock, on the same incoming history. -/
theorem history_three_sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (criterion : ThreeHistory s.val sk rs wk) : W σ 3 s := by
  rcases criterion with immediate | king | rook
  · obtain ⟨v, edge, goal⟩ := (admitted_immediate_iff material ongoing turn).mpr immediate
    have mate : W σ 2 v := Or.inl goal
    exact Or.inr ⟨ongoing, Or.inl ⟨turn, v, edge, mate⟩⟩
  · obtain ⟨t, u, distance, notRook, far, last, legal, reply, clear⟩ := king
    exact clear_entry_wins material ongoing turn legal
      (canonical_king_material material turn distance notRook far) last reply clear
  · obtain ⟨t, u, _, _, _, last, legal, reply, clear⟩ := rook
    exact clear_entry_wins material ongoing turn legal
      (KRKMatingMove.rook_move_model material turn legal rfl).1 last reply clear

/-- Complete strong-turn RAW outcome for h>=96. The only history queries
are the two original keys in an ordinary entry, with mate handled directly. -/
theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace) :
    F σ s ↔ ThreeHistory s.val sk rs wk := by
  constructor
  · rintro ⟨n, win⟩
    cases n with
    | zero => exact False.elim (opp_ne σ (turn.symm.trans win.1))
    | succ n =>
      rcases win with goal | ⟨_, chosen | defended⟩
      · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
      · obtain ⟨_, v, edge, child⟩ := chosen
        have childWin : F σ v := ⟨n, child⟩
        obtain ⟨_, clock⟩ := winning_child_quiet material edge childWin
        obtain ⟨m, legal, rawEq⟩ := edge
        have endpoint : erase v = play (erase s) m := congrArg RawTrace.erase rawEq
        obtain ⟨ns, nr, next⟩ := krk_strong_material material turn legal
        have nextV : IsKRK (erase v) σ ns nr wk := by rwa [endpoint]
        have nextTurn : (erase v).turn = σ.opp := by rw [endpoint, play_turn, turn]
        by_cases childOngoing : Ongoing v
        · obtain ⟨last, noClaim⟩ := (KRKLastReply.high_clock_force_iff nextV childOngoing nextTurn (by omega)).mp childWin
          obtain ⟨u, reply, _⟩ := unique_legal_reply next
            (by rw [play_turn, turn]) (KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next) last
          have absent : ¬RawClaims.AvailableThreshold (RawTrace.append s.val m legal) := by
            change ¬RawClaims.AvailableThreshold v.val at noClaim
            rwa [rawEq] at noClaim
          have clear := (entry_no_claim_iff material turn legal next last reply).mp absent
          rcases last_entry_move material turn legal next last with
            ⟨src, promo, distance, moved, geometry⟩ | ⟨src, promo, sees, moved, geometry⟩
          · have canonical : m = ⟨sk, m.dst, none⟩ := by cases m; simp only [Move.mk.injEq]; exact ⟨src, True.intro, promo⟩
            right; left
            refine ⟨m.dst, u, distance, moved.1, KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ moved, geometry, ?_, ?_, ?_⟩
            · rw [←canonical]; exact legal
            · rw [←canonical]; exact reply
            · rw [←canonical]; exact clear
          · have canonical : m = ⟨rs, m.dst, none⟩ := by cases m; simp only [Move.mk.injEq]; exact ⟨src, True.intro, promo⟩
            right; right
            refine ⟨m.dst, u, sees, Ne.symm moved.1, moved.2.2.1, geometry, ?_, ?_, ?_⟩
            · rw [←canonical]; exact legal
            · rw [←canonical]; exact reply
            · rw [←canonical]; exact clear
        · have goal := (terminal_force_iff_goal childOngoing).mp childWin
          exact Or.inl ((admitted_immediate_iff material ongoing turn).mp ⟨v, ⟨m, legal, rawEq⟩, goal⟩)
      · exact False.elim (opp_ne σ (turn.symm.trans defended.1))
  · intro criterion
    exact ⟨3, history_three_sufficient material ongoing turn criterion⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace) :
    ActualWin σ s ↔ ThreeHistory s.val sk rs wk :=
  (actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

/-- Failure of the coordinate/barrier test gives a holding policy against
every legal strong alternative, including castling. -/
theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace) :
    RuleHold σ.opp s ↔ ¬ThreeHistory s.val sk rs wk := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high] using dual

/-- The high-clock strong winning region has distance at most three.
Outside immediate mate, no certificate of distance at most two exists. -/
theorem high_clock_exact_three {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace) :
    (F σ s ↔ W σ 3 s) ∧ (¬MateNow sk rs wk → ¬W σ 2 s) := by
  constructor
  · constructor
    · intro win
      exact history_three_sufficient material ongoing turn
        ((high_clock_force_iff material ongoing turn high).mp win)
    · intro win; exact ⟨3, win⟩
  · intro notImmediate win
    have one := strong_two_to_one turn (raw_ruleMateWithin_project s σ 2 win)
    rcases one with goal | ⟨_, chosen | defended⟩
    · exact opp_ne σ (turn.symm.trans goal.1)
    · obtain ⟨_, r, legal, goal⟩ := chosen
      obtain ⟨v, edge, endpoint⟩ := layer.reply_complete ongoing legal
      change erase v = r at endpoint
      apply notImmediate
      apply (admitted_immediate_iff material ongoing turn).mp
      refine ⟨v, edge, ?_⟩
      change MateGoal σ (erase v)
      rwa [endpoint]
    · exact opp_ne σ (turn.symm.trans defended.1)

end EndgameChess.Rules.KRKThreePly
