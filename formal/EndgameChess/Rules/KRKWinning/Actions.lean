import EndgameChess.Rules.KRKWinning.Definitions
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- Full forcing retains every opponent move and forbids every correct opponent claim. -/
theorem forcing_actions {c : Colour} {s : State} (ongoing : Ongoing s) (win : F c s) :
    ((erase s).turn = c → ∃ t, BoardStep s t ∧ F c t) ∧
    ((erase s).turn = c.opp → ¬CanClaim s ∧ ∀ t, BoardStep s t → F c t) := by
  have notGoal : ¬G c s := by
    intro goal
    exact goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1)
  obtain ⟨n,certificate⟩ := win
  cases n with
  | zero => exact False.elim (notGoal certificate)
  | succ n =>
    rcases certificate with goal | ⟨_,chosen | defended⟩
    · exact False.elim (notGoal goal)
    · obtain ⟨turn,t,edge,child⟩ := chosen
      exact ⟨fun _ => ⟨t,edge,n,child⟩,
        fun opposite => False.elim (opp_ne c (turn.symm.trans opposite))⟩
    · obtain ⟨turn,noClaim,_,all⟩ := defended
      exact ⟨fun own => False.elim (opp_ne c (own.symm.trans turn)),
        fun _ => ⟨noClaim,fun t edge => ⟨n,all t edge⟩⟩⟩
end EndgameChess.Rules.KRKWinning
