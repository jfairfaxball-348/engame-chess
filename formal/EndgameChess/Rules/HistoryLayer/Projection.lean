import EndgameChess.Rules.HistoryLayer.Definitions

/-! S033 / EC-C022: same-budget projection to the frozen finite-rank game. -/
namespace EndgameChess.Rules.HistoryLayer
open EndgameChess.KK

universe u

/-- A rule-layer finite mate certificate projects with the identical board-ply
budget. Every raw defending reply is covered via the layer completeness field. -/
theorem ruleMateWithin_project {State : Type u} (L : Layer State)
    {σ : Colour} {n : Nat} {s : State} (h : RuleMateWithin L σ n s) :
    MateWithin σ n (L.erase s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    rcases h with hg | ⟨ho, hc | hd⟩
    · exact Or.inl hg
    · obtain ⟨ht, t, hstep, hwin⟩ := hc
      exact Or.inr ⟨L.ongoing_not_dead ho,
        Or.inl ⟨ht, L.erase t, L.step_sound ho hstep, ih hwin⟩⟩
    · obtain ⟨ht, _, ⟨t, hstep⟩, hall⟩ := hd
      refine Or.inr ⟨L.ongoing_not_dead ho,
        Or.inr ⟨ht, ⟨L.erase t, L.step_sound ho hstep⟩, ?_⟩⟩
      intro r hr
      obtain ⟨t, hs, he⟩ := L.reply_complete ho hr
      have hw := ih (hall t hs)
      rwa [he] at hw

end EndgameChess.Rules.HistoryLayer
