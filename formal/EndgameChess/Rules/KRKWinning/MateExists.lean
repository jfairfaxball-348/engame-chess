import EndgameChess.Rules.KRKWinning.MaximalGoal
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding KRKTermination

/-- A real admitted terminal named-mate continuation exists within the KRK fuel cap. -/
theorem winning_mate_continuation {σ c : Colour} {π : Policy} {s : State}
    (region : Region σ s) (legal : LegalPolicy c π) (safe : WinningSafety c π s) :
    ∃ n t, PolicyPath c π n s t ∧ ¬Ongoing t ∧ G c t ∧ n ≤ fuel s := by
  obtain ⟨n,t,path,stopped,bound⟩ := stopped_continuation legal s region
  rcases stopped with terminal | ⟨ongoing,own,claim,_⟩
  · exact ⟨n,t,path,terminal,(safe n t path).1 terminal,bound⟩
  · exact False.elim (((safe n t path).2 ongoing).1 own claim)
end EndgameChess.Rules.KRKWinning
