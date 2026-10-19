import EndgameChess.Rules.RawTrace.Definitions

/-! S035 / EC-C023: exact played endpoint and full ordered-prefix retention. -/
namespace EndgameChess.Rules.RawTrace

theorem append_spec (s : State) (m : Move) (h : isLegal (erase s) m = true) :
    erase (append s m h) = play (erase s) m ∧
    (append s m h).trace.moves = s.trace.moves ++ [m] ∧
    (append s m h).trace.positions = s.trace.positions ++ [play (erase s) m] ∧
    (append s m h).trace.moves.length = s.trace.moves.length + 1 := by
  exact ⟨rfl, rfl, rfl, by simp [append, Trace.moves]⟩

end EndgameChess.Rules.RawTrace
