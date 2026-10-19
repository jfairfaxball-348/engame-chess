import EndgameChess.Rules.Reach

/-! S035 / EC-C023: concrete move data rooted at initial, not FIDE adjudication.
The move witness and prior trace are data; legality evidence is proof-only. -/
namespace EndgameChess.Rules.RawTrace

/-- Raw kernel traces store every actual move. No earlier-terminal filter. -/
inductive Trace : Position → Type
  | start : Trace initial
  | snoc {q : Position} (prior : Trace q) (m : Move)
      (legal : isLegal q m = true) : Trace (play q m)

/-- Ordered actual moves, including promotion choices. -/
def Trace.moves {q : Position} (t : Trace q) : List Move :=
  match t with
  | .start => []
  | .snoc prior m _ => prior.moves ++ [m]

/-- Ordered full positions, including both initial and current endpoints. -/
def Trace.positions {q : Position} (t : Trace q) : List Position :=
  match t with
  | .start => [initial]
  | @Trace.snoc q prior m _ => prior.positions ++ [play q m]

structure State where
  endpoint : Position
  trace : Trace endpoint

def erase (s : State) : Position := s.endpoint

def initialState : State := ⟨initial, .start⟩

/-- Append the given legal move and preserve its exact prior trace. -/
def append (s : State) (m : Move) (h : isLegal (erase s) m = true) : State :=
  ⟨play (erase s) m, .snoc s.trace m h⟩

/-- A step is an actual one-move trace extension, not just related erasures. -/
def RawBoardStep (s t : State) : Prop :=
  ∃ m, ∃ h : isLegal (erase s) m = true, t = append s m h

end EndgameChess.Rules.RawTrace
