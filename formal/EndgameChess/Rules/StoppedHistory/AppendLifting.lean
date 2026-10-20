import EndgameChess.Rules.StoppedHistory.Definitions

/-! S062 / EC-C037: actual append and EVERY legal reply, including terminal children. -/
namespace EndgameChess.Rules.StoppedHistory

/-- Exact append guards and full reply lifting relative to raw endpoint status. -/
theorem append_and_reply_lifting (s : RawTrace.State) :
    (∀ (m : Move) (hm : isLegal (RawTrace.erase s) m = true),
      Admissible (RawTrace.append s m hm).trace ↔
        Admissible s.trace ∧ RawAdjudication.classify s = .ongoing) ∧
    (Admissible s.trace → RawAdjudication.classify s = .ongoing →
      ∀ r, Legal (RawTrace.erase s) r →
        ∃ t, Admissible t.trace ∧ RawTrace.RawBoardStep s t ∧
          RawTrace.erase t = r) := by
  have guard : ∀ (m : Move) (hm : isLegal (RawTrace.erase s) m = true),
      Admissible (RawTrace.append s m hm).trace ↔
        Admissible s.trace ∧ RawAdjudication.classify s = .ongoing := by
    intro m hm
    cases s
    exact Iff.rfl
  refine ⟨guard, ?_⟩
  intro admissible ongoing r legal
  obtain ⟨m, hm, rfl⟩ := legal
  exact ⟨RawTrace.append s m hm, (guard m hm).mpr ⟨admissible, ongoing⟩,
    ⟨m, hm, rfl⟩, rfl⟩

end EndgameChess.Rules.StoppedHistory
