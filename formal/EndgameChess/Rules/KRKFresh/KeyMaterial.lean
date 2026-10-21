import EndgameChess.Rules.KRKFresh.Definitions
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK

/-- Normalized key equality preserves exact KRK board material. -/
theorem key_material {σ : Colour} {q r : Position}
    (same : RawRepetition.key q = RawRepetition.key r) (query : Query σ r) : Query σ q := by
  obtain ⟨sk,rs,wk,material⟩ := query
  have boards := congrArg Position.board same
  change q.board = r.board at boards
  exact ⟨sk,rs,wk,material.1,material.2.1,material.2.2.1,boards.trans material.2.2.2⟩
end EndgameChess.Rules.KRKFresh
