import EndgameChess.Rules.KRKHighClock.Definitions
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Every admitted move preserves KRK-or-dead, including castling and rook capture. -/
theorem good_step {σ : Colour} {s t : State} (good : Good σ s)
    (edge : BoardStep s t) : Good σ t := by
  have ongoing := step_parent_ongoing edge
  have nondead := ((RawAdjudication.ongoing_iff s.val).mp ongoing).1
  obtain ⟨sk,rs,wk,material⟩ := good.resolve_right nondead
  obtain ⟨m,hm,endpoint⟩ := edge
  have erased : erase t = play (erase s) m := by
    change RawTrace.erase t.val = _
    rw [endpoint]
    rfl
  rcases krk_legal_material_clock material hm with ⟨ns,nr,nw,next,_⟩ | ⟨_,_,_,dead⟩
  · exact Or.inl ⟨ns,nr,nw,by rwa [erased]⟩
  · exact Or.inr (by rwa [erased])
end EndgameChess.Rules.KRKHighClock
