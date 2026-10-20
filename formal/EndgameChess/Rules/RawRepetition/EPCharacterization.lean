import EndgameChess.Rules.RawRepetition.Definitions

/-! S046 / EC-C029: recover the ep marker/flank from actual legal pawn shape. -/
namespace EndgameChess.Rules.RawRepetition

/-- A legal pawn move changing files into an empty destination is exactly LegalEP. -/
theorem legalEP_iff_shape (q : Position) (m : Move) :
    LegalEP q m ↔ isLegal q m = true ∧ RawClock.Pawn q m ∧
      m.src.1 ≠ m.dst.1 ∧ q.board m.dst = none := by
  constructor
  · intro event
    exact ⟨event.1, event.2.1, event.2.2.2.1, event.2.2.2.2.1⟩
  · rintro ⟨legal, pawn, files, empty⟩
    have source := pawn
    change q.board m.src = some ⟨q.turn, .pawn⟩ at source
    have nonzero : dx m.src m.dst ≠ 0 := by
      intro displacement
      apply files
      apply Fin.ext
      simp only [dx] at displacement
      omega
    have pseudo : isPseudo q m = true := by
      have h := legal
      simp only [isLegal, Bool.and_eq_true] at h
      exact h.1
    have pawnMove : pawnMoveOK q m = true := by
      simp only [isPseudo, source, beq_self_eq_true, Bool.true_and, Bool.and_eq_true] at pseudo
      exact pseudo.2.1
    have ep := pawnMove
    simp [pawnMoveOK, nonzero, empty, Bool.and_eq_true, beq_iff_eq] at ep
    exact ⟨legal, pawn, ep.1.2, files, empty, ep.2⟩

end EndgameChess.Rules.RawRepetition
