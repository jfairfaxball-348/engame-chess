import EndgameChess.Rules.KQK.Complete

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private def Region (σ : Colour) (q : Position) : Prop :=
  (∃ sk qs wk, IsKQK q σ sk qs wk ∧ 2 ≤ dInf sk wk ∧ q.castling = noRights) ∨ DeadK q

private theorem region_step {σ : Colour} {q r : Position}
    (hq : Region σ q) (hl : Legal q r) : Region σ r := by
  rcases hq with ⟨sk,qs,wk,hm,hfar,rights⟩ | dead
  · have nextRights := noRights_after_legal rights hl
    rcases colour_cases σ q.turn with turn | turn
    · rcases strong_reply hm turn rights hl with ⟨s,hs,_,_,_,far⟩ |
          ⟨s,hs,_,_,_,_,far⟩
      · exact Or.inl ⟨s,qs,wk,hs,far,nextRights⟩
      · exact Or.inl ⟨sk,s,wk,hs,far,nextRights⟩
    · rcases LoneKing.weak_cases hm turn hl with ⟨t,hs,_⟩ | ⟨w,b,hkk⟩
      · have safe := legal_mover_safe hl
        rw [turn] at safe
        have h0 : dInf sk t ≠ 0 := fun h => hs.2.1 (dInf_eq_zero_iff.mp h)
        have h1 : dInf sk t ≠ 1 := by
          intro h
          have check := (weak_check hs).mpr (Or.inl h)
          rw [safe] at check; cases check
        exact Or.inl ⟨sk,qs,t,hs,by omega,nextRights⟩
      · exact Or.inr (dead_of_legal_into_KK hl hkk)
  · right
    rintro ⟨t,reach,mate⟩
    exact dead ⟨t,reachK_cons hl reach,mate⟩

/-- A lone king cannot force mate against king and queen, including lines
where the queen is captured. This is independent of strong-side entry. -/
theorem no_weak_force {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (hfar : 2 ≤ dInf sk wk)
    (rights : q.castling = noRights) : ¬ ForceMate σ.opp q := by
  rintro ⟨n,win⟩
  obtain ⟨t,reach,goal⟩ := mateWithin_sound win
  have closure : Region σ t := by
    clear goal
    induction reach with
    | refl => exact Or.inl ⟨sk,qs,wk,hq,hfar,rights⟩
    | tail _ step ih => exact region_step ih step
  rcases closure with ⟨s,x,w,hm,far,_⟩ | dead
  · have tt : t.turn = σ := by simpa only [opp_opp] using goal.1
    have check : inCheck t σ = true := by simpa only [tt] using goal.2.1
    have adjacent := (strong_check hm).mp check
    rw [dInf_comm] at adjacent
    omega
  · exact dead ⟨t,ReachK.refl t,goal.2⟩

/-- Strong-side holding can use any legal policy: no cooperative line in
the closed KQK/KK region ever mates the strong king. -/
theorem no_weak_reachable_mate {q t : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (hfar : 2 ≤ dInf sk wk)
    (rights : q.castling = noRights) (reach : ReachK q t) : ¬ MateGoal σ.opp t := by
  intro goal
  have closure : Region σ t := by
    clear goal
    induction reach with
    | refl => exact Or.inl ⟨sk,qs,wk,hq,hfar,rights⟩
    | tail _ step ih => exact region_step ih step
  rcases closure with ⟨s,x,w,hm,far,_⟩ | dead
  · have tt : t.turn = σ := by simpa only [opp_opp] using goal.1
    have check : inCheck t σ = true := by simpa only [tt] using goal.2.1
    have adjacent := (strong_check hm).mp check
    rw [dInf_comm] at adjacent
    omega
  · exact dead ⟨t,ReachK.refl t,goal.2⟩

/-- Both players lack a forced mate when the weak side can take the queen.
This is the board-game capture boundary, not yet the full fresh WDL50 theorem. -/
theorem unsafe_weak_no_forcing {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hfar : 2 ≤ dInf sk wk) (rights : q.castling = noRights)
    (unsafeQueen : ¬ SafeQueen sk qs wk) :
    ¬ ForceMate σ q ∧ ¬ ForceMate σ.opp q :=
  ⟨fun win => unsafeQueen (force_weak_safe hq ht win),no_weak_force hq hfar rights⟩

end EndgameChess.Rules.KQK
