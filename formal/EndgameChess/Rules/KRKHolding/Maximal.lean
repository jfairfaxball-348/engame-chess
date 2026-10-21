import EndgameChess.Rules.KRKHolding.Definitions
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- A maximal compliant board path ends terminal or at its legal chosen claim. -/
theorem policy_maximal_iff_stopped {c : Colour} {π : Policy}
    (legal : LegalPolicy c π) (s : State) : PolicyMaximal c π s ↔ Stopped c π s := by
  classical
  constructor
  · intro maximal
    by_cases ongoing : Ongoing s
    · right
      by_cases own : (erase s).turn = c
      · have allowed := legal s ongoing own
        cases value : π s with
        | none => exact ⟨ongoing,own,rfl,by rwa [value] at allowed⟩
        | some t =>
          have edge : BoardStep s t := by rwa [value] at allowed
          exact False.elim (maximal ⟨t,edge,fun _ => value⟩)
      · obtain ⟨r,move⟩ := ((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1
        obtain ⟨t,edge,_⟩ := layer.reply_complete ongoing move
        exact False.elim (maximal ⟨t,edge,fun h => False.elim (own h)⟩)
    · exact Or.inl ongoing
  · rintro (terminal | ⟨_,own,value,_⟩) ⟨t,edge,choice⟩
    · exact terminal (step_parent_ongoing edge)
    · have selected := choice own
      rw [value] at selected
      cases selected
end EndgameChess.Rules.KRKHolding
