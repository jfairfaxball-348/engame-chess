import EndgameChess.Rules.KRKTermination.Guard
import EndgameChess.Rules.KRKTermination.Closure
namespace EndgameChess.Rules.KRKTermination
open EndgameChess.KK
open RawHistoryLayer

/-- Every admitted board move preserves the region and consumes at least one fuel. -/
theorem step_decreases {σ : Colour} {s t : State} (region : Region σ s)
    (step : BoardStep s t) : Region σ t ∧ fuel t + 1 ≤ fuel s := by
  classical
  have parent := step_parent_ongoing step
  have parentClock := ((RawAdjudication.ongoing_iff s.val).mp parent).2.2.1
  obtain ⟨sk, rs, wk, material⟩ := region.resolve_right (not_not_intro parent)
  obtain ⟨m, hm, endpoint⟩ := step
  change isLegal (erase s) m = true at hm
  have erased : erase t = play (erase s) m := by
    change RawTrace.erase t.val = _
    rw [endpoint]
    rfl
  have nextClock : RawClock.clock t.val.trace =
      if RawClock.zeroing (erase s) m then 0 else RawClock.clock s.val.trace + 1 := by
    rw [endpoint]
    exact RawClock.append_clock s.val m hm
  rcases krk_legal_material_clock material hm with ⟨ns,nr,nw,next,quiet⟩ | ⟨w,b,_,dead⟩
  · have nextRegion : Region σ t := Or.inl ⟨ns,nr,nw,by rwa [erased]⟩
    refine ⟨nextRegion, ?_⟩
    by_cases ongoing : Ongoing t
    · have childClock := ((RawAdjudication.ongoing_iff t.val).mp ongoing).2.2.1
      simp only [quiet, Bool.false_eq_true, ↓reduceIte] at nextClock
      simp only [fuel, if_pos parent, if_pos ongoing]
      omega
    · simp only [fuel, if_pos parent, if_neg ongoing]
      omega
  · have terminal : ¬Ongoing t := by
      intro ongoing
      have notDead := ((RawAdjudication.ongoing_iff t.val).mp ongoing).1
      apply notDead
      change DeadK (erase t)
      rwa [erased]
    refine ⟨Or.inr terminal, ?_⟩
    simp only [fuel, if_pos parent, if_neg terminal]
    omega
end EndgameChess.Rules.KRKTermination
