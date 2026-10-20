import EndgameChess.Rules.RawTrace.Definitions

/-! S038 / EC-C025: finite actual trace extensions, measured in board plies. -/
namespace EndgameChess.Rules.RawTrace

/-- Zero retains the exact state; each successor appends one actual legal move. -/
inductive Extends : Nat → State → State → Prop
  | refl (s : State) : Extends 0 s s
  | snoc {n : Nat} {s u t : State} :
      Extends n s u → RawBoardStep u t → Extends (n + 1) s t

end EndgameChess.Rules.RawTrace
