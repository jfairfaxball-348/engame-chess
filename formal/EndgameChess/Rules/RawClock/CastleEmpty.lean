import EndgameChess.Rules.RawClock.Definitions
namespace EndgameChess.Rules.RawClock

/-- The actual castling predicate forces an empty destination. -/
theorem castle_empty (q : Position) (m : Move) (h : canCastle q m = true) :
    q.board m.dst = none := by
  simp only [canCastle, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at h
  rcases h with ⟨⟨⟨_, hr⟩, _⟩, hk | hq⟩
  · have hf := hk.1.1.1.1.1.1.1
    have he := hk.1.1.1.2
    have hd : m.dst = ((6 : Fin 8), homeRank q.turn) := Prod.ext hf hr
    simpa only [hd] using he
  · have hf := hq.1.1.1.1.1.1.1.1
    have he := hq.1.1.1.1.2
    have hd : m.dst = ((2 : Fin 8), homeRank q.turn) := Prod.ext hf hr
    simpa only [hd] using he

end EndgameChess.Rules.RawClock
