import EndgameChess.Rules.KRKHolding.Definitions
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer

/-- Any actual legal holding policy refutes EVERY finite opponent certificate. -/
theorem not_force_of_hold {c : Colour} {s : State} (hold : RuleHold c s) : ¬F c.opp s := by
  classical
  obtain ⟨π,legal,safe⟩ := hold
  rintro ⟨n,win⟩
  induction n generalizing s with
  | zero => exact safe 0 s (.refl s) win
  | succ n ih =>
    rcases win with goal | ⟨ongoing,chosen | defended⟩
    · exact safe 0 s (.refl s) goal
    · obtain ⟨turn,t,edge,child⟩ := chosen
      apply ih (s := t) ?_ child
      intro k u path
      apply safe (k+1) u
      refine .cons edge ?_ path
      intro same
      exact False.elim (opp_ne c (same.symm.trans turn))
    · obtain ⟨turn,noClaim,_,all⟩ := defended
      have ownTurn : (erase s).turn = c := by
        change (erase s).turn = c.opp.opp at turn
        simpa only [opp_opp] using turn
      have policyLegal := legal s ongoing ownTurn
      cases value : π s with
      | none =>
        rw [value] at policyLegal
        exact noClaim policyLegal
      | some t =>
        rw [value] at policyLegal
        apply ih (s := t) ?_ (all t policyLegal)
        intro k u path
        exact safe (k+1) u (.cons policyLegal (fun _ => value) path)
end EndgameChess.Rules.KRKHolding
