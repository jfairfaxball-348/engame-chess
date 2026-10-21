import EndgameChess.Rules.KRKHighClock.Definitions
namespace EndgameChess.Rules.KRKHighClock
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- A certified winning child cannot be dead capture; its KRK move increments the clock. -/
theorem winning_child_quiet {σ : Colour} {s t : State} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (edge : BoardStep s t) (win : F σ t) :
    (∃ ns nr nw, IsKRK (erase t) σ ns nr nw) ∧
      RawClock.clock t.val.trace = RawClock.clock s.val.trace + 1 := by
  obtain ⟨m,hm,endpoint⟩ := edge
  have erased : erase t = play (erase s) m := by
    change RawTrace.erase t.val = _
    rw [endpoint]
    rfl
  rcases krk_legal_material_clock material hm with ⟨ns,nr,nw,next,quiet⟩ | ⟨_,_,_,dead⟩
  · refine ⟨⟨ns,nr,nw,by rwa [erased]⟩,?_⟩
    have clock : RawClock.clock t.val.trace =
        if RawClock.zeroing (erase s) m then 0 else RawClock.clock s.val.trace + 1 := by
      rw [endpoint]
      exact RawClock.append_clock s.val m hm
    simpa only [quiet, Bool.false_eq_true, ↓reduceIte] using clock
  · obtain ⟨n,certificate⟩ := win
    have projected := raw_ruleMateWithin_project t σ n certificate
    exact False.elim (forceMate_not_dead ⟨n,projected⟩ (by rwa [erased]))
end EndgameChess.Rules.KRKHighClock
