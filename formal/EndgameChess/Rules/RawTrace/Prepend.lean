import EndgameChess.Rules.RawTrace.ExtensionDefinitions

/-! S066 / EC-C039 prerequisite: prepend an actual step to an actual extension. -/
namespace EndgameChess.Rules.RawTrace

theorem extends_prepend {s u t : State} (step : RawBoardStep s u)
    {n : Nat} (path : Extends n u t) : Extends (n + 1) s t := by
  induction path with
  | refl => exact Extends.snoc (Extends.refl s) step
  | snoc prior last ih => exact Extends.snoc (ih step) last

end EndgameChess.Rules.RawTrace
