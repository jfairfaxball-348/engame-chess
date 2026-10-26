import EndgameChess.Rules.KRKImmediate
import EndgameChess.Rules.KRKTermination.Strong

namespace EndgameChess.Rules.KRKEdgeDepth
open EndgameChess.KK KRKMateGeometry KRKImmediate
set_option maxHeartbeats 200000

def depth (wk : Square) : Nat :=
  min (min wk.1.val (7 - wk.1.val)) (min wk.2.val (7 - wk.2.val))

theorem depth_step {wk t : Square} (step : dInf wk t = 1) : depth wk ≤ depth t + 1 := by
  simp only [depth, dInf, absDiff] at step ⊢
  omega

theorem terminal_depth_zero {sk rs wk : Square} (terminal : Terminal sk rs wk) :
    depth wk = 0 := by
  rcases terminal with horizontal | vertical
  · have edge := horizontal.2.1
    simp only [depth]; omega
  · have edge := vertical.2.1
    dsimp only at edge
    simp only [depth]; omega

private theorem horizontal_predecessor {sk dst wk t : Square}
    (far : 2 ≤ dInf sk wk) (step : dInf wk t = 1)
    (terminal : Horizontal sk dst t) : wk.2.val = t.2.val := by
  obtain ⟨_, edge, _, left, right, middle⟩ := terminal
  simp only [dInf, absDiff] at far step
  omega

/-- The last weak step before immediate mate must already start on an edge.
This includes the shifted-king corner templates. -/
theorem ready_predecessor_depth_zero {sk rs wk t : Square}
    (far : 2 ≤ dInf sk wk) (step : dInf wk t = 1)
    (ready : MateNow sk rs t) : depth wk = 0 := by
  rcases ready with ⟨horizontal, _⟩ | ⟨vertical, _⟩
  · have same := horizontal_predecessor far step horizontal
    have edge := horizontal.2.1
    simp only [depth]; omega
  · have same := horizontal_predecessor
      (sk := symSwap.f sk) (wk := symSwap.f wk) (t := symSwap.f t)
      (by rwa [symSwap.dInf_eq]) (by rwa [symSwap.dInf_eq]) vertical
    have edge := vertical.2.1
    dsimp only [symSwap] at same edge
    simp only [depth]; omega

private theorem weak_one_goal {σ : Colour} {q : Position}
    (turn : q.turn = σ.opp) (win : MateWithin σ 1 q) : MateGoal σ q := by
  rcases win with goal | ⟨_, chosen | defended⟩
  · exact goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · obtain ⟨r, legal⟩ := defended.2.1
    have goal := defended.2.2 r legal
    have nextTurn : r.turn = σ := by rw [turn_of_legal legal, turn, opp_opp]
    exact False.elim (opp_ne σ (nextTurn.symm.trans goal.1))

private theorem strong_two_immediate {σ : Colour} {q : Position}
    (turn : q.turn = σ) (win : MateWithin σ 2 q) :
    ∃ r, Legal q r ∧ MateGoal σ r := by
  rcases win with goal | ⟨_, chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_, r, legal, child⟩ := chosen
    exact ⟨r, legal, weak_one_goal (by rw [turn_of_legal legal, turn]) child⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem weak_interior_not_three {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (inside : 0 < depth wk) : ¬MateWithin σ 3 q := by
  intro win
  have safe := krk_force_weak_safe material turn ⟨3, win⟩
  rcases win with goal | ⟨_, chosen | defended⟩
  · have zero := terminal_depth_zero ((kernel_mate_iff material turn far).mp goal.2)
    omega
  · exact opp_ne σ (chosen.1.symm.trans turn)
  · obtain ⟨r, legal⟩ := defended.2.1
    obtain ⟨t, next, step⟩ := krk_safe_reply material turn safe legal
    have child := strong_two_immediate next.2 (defended.2.2 r legal)
    obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry legal next.1 next.2
    have ready := (immediate_iff next.1 next.2 nextFar notCheck).mp child
    have distance : dInf wk t = 1 := by cases step with | lone h _ _ _ => exact h
    have zero := ready_predecessor_depth_zero far distance ready
    omega

private theorem strong_child_separated {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (safe : inCheck q σ = false) : 2 ≤ dInf sk wk := by
  have nz : dInf sk wk ≠ 0 := fun h => hk.2.1 (dInf_eq_zero_iff.mp h)
  have noOne : dInf sk wk ≠ 1 := by
    intro h
    have check := (inCheck_strong_krk hk.1 hk.2.1 hk.2.2.1 hk.2.2.2).mpr
      (by rwa [dInf_comm])
    rw [check] at safe
    cases safe
  omega

theorem arrival_far {p q : Position} {σ : Colour} {sk rs wk : Square}
    (legal : Legal p q) (material : IsKRK q σ sk rs wk) : 2 ≤ dInf sk wk := by
  rcases colour_cases σ q.turn with strong | weak
  · exact (krk_strong_arrival_geometry legal material strong).1
  · have parentTurn : p.turn = σ := by
      have alternating := turn_of_legal legal
      rw [weak] at alternating
      have same := congrArg Colour.opp alternating
      simpa only [opp_opp] using same.symm
    have safe := legal_mover_safe legal
    rw [parentTurn] at safe
    exact strong_child_separated material safe

/-- Universal necessary budget from positive edge depth. The proof covers all
strong move types and uses unfiltered, nonempty defender replies. -/
theorem mate_depth_lower {σ : Colour} {n : Nat} {q : Position} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (far : 2 ≤ dInf sk wk)
    (inside : 0 < depth wk) (win : MateWithin σ n q) :
    (q.turn = σ → 2 * depth wk + 3 ≤ n) ∧
    (q.turn = σ.opp → 2 * depth wk + 2 ≤ n) := by
  induction n generalizing q sk rs wk with
  | zero =>
    have zero := terminal_depth_zero ((kernel_mate_iff material win.1 far).mp win.2)
    omega
  | succ n ih =>
    have original := win
    rcases win with goal | ⟨_, chosen | defended⟩
    · have zero := terminal_depth_zero ((kernel_mate_iff material goal.1 far).mp goal.2)
      omega
    · obtain ⟨turn, r, legal, child⟩ := chosen
      obtain ⟨m, hm, rfl⟩ := legal
      obtain ⟨ns, nr, next⟩ := krk_strong_material material turn hm
      have safe := not_inCheck_after_legal hm
      rw [turn] at safe
      have childFar := strong_child_separated next safe
      have lower := (ih next childFar inside child).2 (by simp [play_turn, turn])
      constructor
      · intro _; omega
      · intro weak; exact False.elim (opp_ne σ (turn.symm.trans weak))
    · obtain ⟨turn, nonempty, all⟩ := defended
      constructor
      · intro strong; exact False.elim (opp_ne σ (strong.symm.trans turn))
      · intro _
        by_cases shallow : depth wk = 1
        · have notSmall : ¬n + 1 ≤ 3 := by
            intro small
            exact weak_interior_not_three material turn far inside
              (mateWithin_mono original small)
          omega
        · obtain ⟨r, legal⟩ := nonempty
          have safe := krk_force_weak_safe material turn ⟨n + 1, original⟩
          obtain ⟨t, next, step⟩ := krk_safe_reply material turn safe legal
          have distance : dInf wk t = 1 := by cases step with | lone h _ _ _ => exact h
          have childFar : 2 ≤ dInf sk t := by cases step with | lone _ _ h _ => exact h
          have depthBound := depth_step distance
          have childInside : 0 < depth t := by omega
          have lower := (ih next.1 childFar childInside (all r legal)).1 next.2
          change 2 * depth t + 3 ≤ n at lower
          omega

end EndgameChess.Rules.KRKEdgeDepth
