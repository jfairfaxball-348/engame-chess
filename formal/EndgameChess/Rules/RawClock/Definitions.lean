import EndgameChess.Rules.RawTrace.Append
import EndgameChess.Rules.RawTrace.Soundness
import EndgameChess.Rules.RawTrace.Completeness
import EndgameChess.Rules.RawTrace.Origin
import EndgameChess.Rules.KNK

/-! S036 / EC-C024: raw counter only; no game-admissibility or adjudication. -/
namespace EndgameChess.Rules.RawClock

/-- Source-pawn event, before any promotion. -/
def Pawn (q : Position) (m : Move) : Prop :=
  q.board m.src = some ⟨q.turn, .pawn⟩

/-- Meaning as pawn/capture is asserted only for legal moves. -/
def zeroing (q : Position) (m : Move) : Bool :=
  (q.board m.src == some ⟨q.turn, .pawn⟩) || (q.board m.dst).isSome

/-- Ordinary enemy capture or the kernel en-passant capture event. -/
def CaptureEvent (q : Position) (m : Move) : Prop :=
  (∃ pc, q.board m.dst = some pc ∧ pc.colour ≠ q.turn) ∨
  (Pawn q m ∧ q.ep = some m.dst ∧ m.src.1 ≠ m.dst.1 ∧
    q.board m.dst = none ∧ q.board (m.dst.1, m.src.2) = some ⟨q.turn.opp, .pawn⟩)

/-- Board plies since the last reset, derived from full stored data. -/
def clock {q : Position} (t : RawTrace.Trace q) : Nat :=
  match t with
  | .start => 0
  | @RawTrace.Trace.snoc q prior m _ =>
      if zeroing q m then 0 else clock prior + 1

end EndgameChess.Rules.RawClock
