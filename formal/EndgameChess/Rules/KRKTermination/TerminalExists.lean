import EndgameChess.Rules.KRKTermination.PathBound
import EndgameChess.Rules.KRKTermination.Maximal
namespace EndgameChess.Rules.KRKTermination
open EndgameChess.KK
open RawHistoryLayer

/-- A terminal actual admitted continuation exists within the universal fuel cap. -/
theorem terminal_continuation {σ : Colour} (s : State) (region : Region σ s) :
    ∃ n t, Path n s t ∧ ¬Ongoing t ∧ n ≤ fuel s := by
  classical
  generalize value : fuel s = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    by_cases ongoing : Ongoing s
    · obtain ⟨r, legal⟩ := ((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1
      obtain ⟨u, step, _⟩ := layer.reply_complete ongoing legal
      obtain ⟨nextRegion, decrease⟩ := step_decreases region step
      obtain ⟨n,t,path,terminal,bound⟩ := ih (fuel u) (by omega) u nextRegion rfl
      exact ⟨n+1,t,Path.cons step path,terminal,by omega⟩
    · exact ⟨0,s,Path.refl s,ongoing,by omega⟩
end EndgameChess.Rules.KRKTermination
