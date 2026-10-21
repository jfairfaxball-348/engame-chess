import EndgameChess.Rules.KRKHolding.Maximal
import EndgameChess.Rules.KRKHolding.PathBound
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- Every legal policy has a real stopped continuation within the KRK fuel cap. -/
theorem stopped_continuation {σ c : Colour} {π : Policy} (legal : LegalPolicy c π)
    (s : State) (region : Region σ s) :
    ∃ n t, PolicyPath c π n s t ∧ Stopped c π t ∧ n ≤ fuel s := by
  classical
  generalize value : fuel s = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    by_cases stop : Stopped c π s
    · exact ⟨0,s,.refl s,stop,by omega⟩
    · have notMax : ¬PolicyMaximal c π s := by
        intro maximal
        exact stop ((policy_maximal_iff_stopped legal s).mp maximal)
      have successor : ∃ t, BoardStep s t ∧ ((erase s).turn = c → π s = some t) := by
        apply Classical.byContradiction
        intro none
        exact notMax none
      obtain ⟨u,edge,choice⟩ := successor
      obtain ⟨next,dec⟩ := step_decreases region edge
      obtain ⟨n,t,path,ended,bound⟩ := ih (fuel u) (by omega) u next rfl
      exact ⟨n+1,t,.cons edge choice path,ended,by omega⟩
end EndgameChess.Rules.KRKHolding
