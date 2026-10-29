import EndgameChess.Rules.FreshGame.Definitions

namespace EndgameChess.Rules.FreshGame
open EndgameChess.KK

/-- A short stored prefix bounds repetitions without any assumption about its keys. -/
theorem occurrences_le_past (s : State) : occurrences s ≤ s.past.length + 1 := by
  classical
  unfold occurrences
  have bound := List.length_filter_le
    (fun q => decide (RawRepetition.key q = RawRepetition.key s.board)) s.past
  omega

theorem afterMove_clock_le (s : State) (m : Move) : (afterMove s m).clock ≤ s.clock + 1 := by
  dsimp [afterMove]
  split <;> omega

theorem occurrences_one_of_key_ne {s : State}
    (separated : ∀ q ∈ s.past, RawRepetition.key q ≠ RawRepetition.key s.board) :
    occurrences s = 1 := by
  classical
  have empty : s.past.filter (fun q => decide (RawRepetition.key q = RawRepetition.key s.board)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q member same
    exact separated q member (of_decide_eq_true same)
  simp only [occurrences, empty, List.length_nil, Nat.add_zero]

/-- Neither current nor intended draw claims can occur at a fresh root. -/
theorem fresh_no_claim (q : Position) : ¬ CanClaim (fresh q) := by
  have current := occurrences_le_past (fresh q)
  change occurrences (fresh q) ≤ 0 + 1 at current
  rintro (claim | ⟨m, _, claim⟩)
  · rcases claim with clock | repetitions
    · change 100 ≤ 0 at clock; omega
    · omega
  · have clock := afterMove_clock_le (fresh q) m
    have count := occurrences_le_past (afterMove (fresh q) m)
    change (afterMove (fresh q) m).clock ≤ 0 + 1 at clock
    change occurrences (afterMove (fresh q) m) ≤ 1 + 1 at count
    rcases claim with clockClaim | repetitionClaim <;> omega

/-- The immediately previous board never contributes a repetition hit,
because every move changes the turn. -/
theorem afterMove_occurrences_le_past (s : State) (m : Move) :
    occurrences (afterMove s m) ≤ s.past.length + 1 := by
  classical
  have different : RawRepetition.key s.board ≠ RawRepetition.key (play s.board m) := by
    intro same
    have turns : s.board.turn = (play s.board m).turn := by
      simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.turn same
    rw [play_turn] at turns
    exact opp_ne _ turns
  have headFalse : decide (RawRepetition.key s.board = RawRepetition.key (play s.board m)) = false := by
    simp [different]
  change 1 + ((s.board :: s.past).filter
    (fun q => decide (RawRepetition.key q = RawRepetition.key (play s.board m)))).length ≤ _
  simp only [List.filter_cons, headFalse, Bool.false_eq_true, ↓reduceIte]
  have bound := List.length_filter_le
    (fun q => decide (RawRepetition.key q = RawRepetition.key (play s.board m))) s.past
  omega

/-- One preceding board and at most one quiet ply cannot enable either
a current or intended draw claim, including a return to the root board. -/
theorem one_ply_no_claim {s : State} (clock : s.clock ≤ 1) (past : s.past.length ≤ 1) :
    ¬ CanClaim s := by
  have count := occurrences_le_past s
  rintro (claim | ⟨m, _, claim⟩)
  · rcases claim with clockClaim | repetitionClaim <;> omega
  · have nextClock := afterMove_clock_le s m
    have nextCount := afterMove_occurrences_le_past s m
    rcases claim with clockClaim | repetitionClaim <;> omega

/-- In the first three plies only one past board can share the current
turn. Hence even a legal return cannot yet be a third occurrence. -/
theorem three_moves_occurrences_le_two (q : Position) (a b c : Move) :
    occurrences (afterMove (afterMove (afterMove (fresh q) a) b) c) ≤ 2 := by
  classical
  let q1 := play q a
  let q2 := play q1 b
  let q3 := play q2 c
  have ne0 : RawRepetition.key q ≠ RawRepetition.key q3 := by
    intro same
    have turns : q.turn = q3.turn := by
      simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.turn same
    simp only [q3, q2, q1, play_turn, opp_opp] at turns
    exact opp_ne _ turns
  have ne2 : RawRepetition.key q2 ≠ RawRepetition.key q3 := by
    intro same
    have turns : q2.turn = q3.turn := by
      simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.turn same
    simp only [q3, play_turn] at turns
    exact opp_ne _ turns
  change 1 + ([q2, q1, q].filter (fun r => decide (RawRepetition.key r = RawRepetition.key q3))).length ≤ 2
  by_cases middle : RawRepetition.key q1 = RawRepetition.key q3 <;>
    simp [ne0, ne2, middle]

/-- A two-ply prefix and any intended third move still cannot enable a
draw claim. This uses the actual alternating turns, not an erased history. -/
theorem two_ply_no_claim (q : Position) (a b : Move) :
    ¬ CanClaim (afterMove (afterMove (fresh q) a) b) := by
  have clock1 := afterMove_clock_le (fresh q) a
  have clock2 := afterMove_clock_le (afterMove (fresh q) a) b
  have count := afterMove_occurrences_le_past (afterMove (fresh q) a) b
  change (afterMove (fresh q) a).clock ≤ 0 + 1 at clock1
  change occurrences (afterMove (afterMove (fresh q) a) b) ≤ 1 + 1 at count
  rintro (claim | ⟨c, _, claim⟩)
  · rcases claim with clockClaim | repetitionClaim <;> omega
  · have clock3 := afterMove_clock_le (afterMove (afterMove (fresh q) a) b) c
    have count3 := three_moves_occurrences_le_two q a b c
    rcases claim with clockClaim | repetitionClaim <;> omega

end EndgameChess.Rules.FreshGame
