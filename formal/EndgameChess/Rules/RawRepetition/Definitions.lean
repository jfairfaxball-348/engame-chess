import EndgameChess.Rules.RawClock.Definitions

/-! S044 / EC-C028: legality-filtered ep target only, not a full repetition key. -/
namespace EndgameChess.Rules.RawRepetition

open EndgameChess.KK

/-- Actual legal en-passant event, matching the frozen capture-event EP branch. -/
def LegalEP (q : Position) (m : Move) : Prop :=
  isLegal q m = true ∧ RawClock.Pawn q m ∧ q.ep = some m.dst ∧
    m.src.1 ≠ m.dst.1 ∧ q.board m.dst = none ∧
    q.board (m.dst.1, m.src.2) = some ⟨q.turn.opp, .pawn⟩

/-- Suppress a raw ep marker unless an actual legal ep witness exists. -/
noncomputable def effectiveEP (q : Position) : Option Square := by
  classical
  exact if ∃ m, LegalEP q m then q.ep else none

end EndgameChess.Rules.RawRepetition
