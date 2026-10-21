import EndgameChess.Rules.KRKFresh.Definitions
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK

/-- CLOCK-FREE winning children retain KRK; no not-yet-proved RAW certificate used. -/
theorem winning_move_material {σ : Colour} {q : Position} {m : Move}
    (query : Query σ q) (hm : isLegal q m = true) (win : ForceMate σ (play q m)) :
    Query σ (play q m) := by
  obtain ⟨sk,rs,wk,material⟩ := query
  rcases krk_legal_material_clock material hm with ⟨ns,nr,nw,next,_⟩ | ⟨_,_,_,dead⟩
  · exact ⟨ns,nr,nw,next⟩
  · exact False.elim (forceMate_not_dead win dead)
end EndgameChess.Rules.KRKFresh
