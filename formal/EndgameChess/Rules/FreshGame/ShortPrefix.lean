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

end EndgameChess.Rules.FreshGame
