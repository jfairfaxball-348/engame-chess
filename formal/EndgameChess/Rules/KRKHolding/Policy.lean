import EndgameChess.Rules.KRKHolding.Choice
namespace EndgameChess.Rules.KRKHolding
open EndgameChess.KK RawHistoryLayer KRKTermination

/-- A globally legal history policy preserving the full nonforcing invariant. -/
theorem holding_policy (σ c : Colour) : ∃ π : Policy, LegalPolicy c π ∧
    ∀ s t, Region σ s → ¬F c.opp s → Ongoing s →
      (erase s).turn = c → π s = some t → ¬F c.opp t := by
  classical
  let Good (s : State) (a : Option State) : Prop :=
    (Ongoing s → (erase s).turn = c →
      match a with | none => CanClaim s | some t => BoardStep s t) ∧
    (∀ t, Region σ s → ¬F c.opp s → Ongoing s →
      (erase s).turn = c → a = some t → ¬F c.opp t)
  have existsChoice : ∀ s, ∃ a, Good s a := by
    intro s
    by_cases ongoing : Ongoing s
    · by_cases turn : (erase s).turn = c
      · by_cases claim : CanClaim s
        · exact ⟨none,⟨fun _ _ => claim,by intro t _ _ _ _ bad; cases bad⟩⟩
        · by_cases safe : Region σ s ∧ ¬F c.opp s
          · obtain ⟨t,step,notWin⟩ := (defensive_choice safe.1 safe.2 ongoing).2 turn claim
            refine ⟨some t,⟨fun _ _ => step,?_⟩⟩
            intro u _ _ _ _ same
            cases same
            exact notWin
          · obtain ⟨r,legal⟩ := ((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1
            obtain ⟨t,step,_⟩ := layer.reply_complete ongoing legal
            refine ⟨some t,⟨fun _ _ => step,?_⟩⟩
            intro u region notWin
            exact False.elim (safe ⟨region,notWin⟩)
      · exact ⟨none,⟨by intro _ h; exact False.elim (turn h),
          by intro t _ _ _ h; exact False.elim (turn h)⟩⟩
    · exact ⟨none,⟨by intro h; exact False.elim (ongoing h),
        by intro t _ _ h; exact False.elim (ongoing h)⟩⟩
  let π : Policy := fun s => Classical.choose (existsChoice s)
  have good : ∀ s, Good s (π s) := fun s => Classical.choose_spec (existsChoice s)
  exact ⟨π,fun s => (good s).1,fun s t => (good s).2 t⟩
end EndgameChess.Rules.KRKHolding
