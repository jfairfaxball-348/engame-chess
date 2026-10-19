import EndgameChess.Rules.RawTrace.Definitions

/-! S035 / EC-C023: forgetting stored trace data gives raw kernel reachability. -/
namespace EndgameChess.Rules.RawTrace

theorem trace_arisen {q : Position} (t : Trace q) : Arisen q := by
  induction t with
  | start => exact ReachK.refl initial
  | snoc prior m hm ih => exact ReachK.tail ih ⟨m, hm, rfl⟩

end EndgameChess.Rules.RawTrace
