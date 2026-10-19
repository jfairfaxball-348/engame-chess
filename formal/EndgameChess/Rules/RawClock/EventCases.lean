import EndgameChess.Rules.RawClock.Definitions
namespace EndgameChess.Rules.RawClock

/-- Includes every pawn promotion/ep move and every quiet nonpawn move. -/
theorem event_cases (q : Position) (m : Move) :
    (Pawn q m → zeroing q m = true) ∧
    ((∃ pc, q.board m.dst = some pc) → zeroing q m = true) ∧
    (¬ Pawn q m → q.board m.dst = none → zeroing q m = false) := by
  constructor
  · intro h
    change q.board m.src = some ⟨q.turn, .pawn⟩ at h
    simp [zeroing, h]
  constructor
  · rintro ⟨pc, h⟩
    simp [zeroing, h]
  · intro hp hd
    change q.board m.src ≠ some ⟨q.turn, .pawn⟩ at hp
    simp [zeroing, hp, hd]

end EndgameChess.Rules.RawClock
