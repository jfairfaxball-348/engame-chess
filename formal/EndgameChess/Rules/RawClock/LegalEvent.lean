import EndgameChess.Rules.RawClock.Definitions
namespace EndgameChess.Rules.RawClock

/-- Kernel capture-event correspondence; no material-count theorem assumed. -/
theorem legal_zero_iff (q : Position) (m : Move) (hm : isLegal q m = true) :
    zeroing q m = true ↔ Pawn q m ∨ CaptureEvent q m := by
  have hp : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at hm
    exact hm.1
  have ht := targetOK_of_isPseudo hp
  by_cases hw : Pawn q m
  · have hw' := hw
    change q.board m.src = some ⟨q.turn, .pawn⟩ at hw'
    simp [zeroing, hw, hw']
  change q.board m.src ≠ some ⟨q.turn, .pawn⟩ at hw
  cases hd : q.board m.dst with
  | none => simp [zeroing, Pawn, CaptureEvent, hd, hw]
  | some pc =>
    have he := (targetOK_some ht hd).1
    have hc : CaptureEvent q m := Or.inl ⟨pc, hd, he⟩
    simp [zeroing, hd, hc]

end EndgameChess.Rules.RawClock
