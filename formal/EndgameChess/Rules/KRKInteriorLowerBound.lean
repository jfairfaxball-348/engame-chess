import EndgameChess.Rules.KRKFourPlyInterior

namespace EndgameChess.Rules.KRKFourPlyEscape
open EndgameChess.KK KRKLastReply KRKImmediate KRKThreePly KRKMateGeometry
open KRKEdgeDepth

/-- An interior weak king cannot be forced to mate within four plies.
Every legal reply, captures and all strong castling alternatives are retained. -/
theorem weak_interior_not_four {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < depth wk) : ¬MateWithin σ 4 q := by
  intro win
  have safe := krk_force_weak_safe material turn ⟨4, win⟩
  rcases win with goal | ⟨_, chosen | defended⟩
  · have zero := terminal_depth_zero ((kernel_mate_iff material goal.1 far).mp goal.2)
    omega
  · exact opp_ne σ (chosen.1.symm.trans turn)
  · apply interior_four_impossible material.1 inside far safe
    intro u step
    obtain ⟨r, legal, next⟩ := step_sound
      (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
    obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry legal next.1 next.2
    exact (strong_three_iff next.1 next.2 nextFar notCheck).mp (defended.2.2 r legal)

private theorem strong_four_to_three {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (win : MateWithin σ 4 q) : MateWithin σ 3 q := by
  rcases win with goal | ⟨_, chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_, r, ⟨m, legal, rfl⟩, child⟩ := chosen
    obtain ⟨ns, nr, next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn, turn]
    have nextFar := arrival_far ⟨m, legal, rfl⟩ next
    have reduced := (weak_two_iff next nextTurn nextFar).mpr
      ((weak_three_iff next nextTurn nextFar).mp child)
    exact mateWithin_choose turn ⟨m, legal, rfl⟩ reduced
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

private theorem weak_five_to_four {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (win : MateWithin σ 5 q) : MateWithin σ 4 q := by
  have safe := krk_force_weak_safe material turn ⟨5, win⟩
  rcases win with goal | ⟨_, chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · apply mateWithin_defend turn defended.2.1
    intro r legal
    obtain ⟨_, next, _⟩ := krk_safe_reply material turn safe legal
    exact strong_four_to_three next.1 next.2 (defended.2.2 r legal)

theorem weak_interior_not_five {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < depth wk) : ¬MateWithin σ 5 q := by
  intro win
  exact weak_interior_not_four material turn far inside (weak_five_to_four material turn win)

/-- Sharpens the earlier positive-depth necessary budget by two plies. -/
theorem mate_depth_lower {σ : Colour} {n : Nat} {q : Position} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (far : 2 ≤ dInf sk wk)
    (inside : 0 < depth wk) (win : MateWithin σ n q) :
    (q.turn = σ → 2 * depth wk + 5 ≤ n) ∧
    (q.turn = σ.opp → 2 * depth wk + 4 ≤ n) := by
  induction n generalizing q sk rs wk with
  | zero =>
    have zero := terminal_depth_zero ((kernel_mate_iff material win.1 far).mp win.2)
    omega
  | succ n ih =>
    have original := win
    rcases win with goal | ⟨_, chosen | defended⟩
    · have zero := terminal_depth_zero ((kernel_mate_iff material goal.1 far).mp goal.2)
      omega
    · obtain ⟨turn, r, ⟨m, legal, rfl⟩, child⟩ := chosen
      obtain ⟨ns, nr, next⟩ := krk_strong_material material turn legal
      have lower := (ih next (arrival_far ⟨m, legal, rfl⟩ next) inside child).2
        (by rw [play_turn, turn])
      constructor
      · intro _; omega
      · intro weak; exact False.elim (opp_ne σ (turn.symm.trans weak))
    · obtain ⟨turn, nonempty, all⟩ := defended
      constructor
      · intro strong; exact False.elim (opp_ne σ (strong.symm.trans turn))
      · intro _
        by_cases shallow : depth wk = 1
        · have notSmall : ¬n + 1 ≤ 5 := by
            intro small
            exact weak_interior_not_five material turn far inside (mateWithin_mono original small)
          omega
        · obtain ⟨r, legal⟩ := nonempty
          have safe := krk_force_weak_safe material turn ⟨n + 1, original⟩
          obtain ⟨t, next, step⟩ := krk_safe_reply material turn safe legal
          have distance : dInf wk t = 1 := by cases step with | lone h _ _ _ => exact h
          have childFar : 2 ≤ dInf sk t := by cases step with | lone _ _ h _ => exact h
          have depthBound := depth_step distance
          have childInside : 0 < depth t := by omega
          have lower := (ih next.1 childFar childInside (all r legal)).1 next.2
          change 2 * depth t + 5 ≤ n at lower
          omega

end EndgameChess.Rules.KRKFourPlyEscape
