import EndgameChess.Rules.FreshGame.Holding

namespace EndgameChess.Rules.FreshGame
open EndgameChess.KK

def WinningSafety (c : Colour) (π : Policy) (s : State) : Prop :=
  ∀ n t, PolicyPath c π n s t →
    (¬ Ongoing t → MateGoal c t.board) ∧
    (Ongoing t → (t.board.turn = c → π t ≠ none) ∧
      (t.board.turn = c.opp → ¬ CanClaim t))

/-- Independent policy semantics: all maximal compliant plays end in the
named mate, opponent draw claims are preserved, and the horizon is uniform. -/
def ActualWin (c : Colour) (s : State) : Prop :=
  ∃ π, ∃ B : Nat, LegalPolicy c π ∧ WinningSafety c π s ∧
    ∀ n t, PolicyPath c π n s t → n ≤ B

private theorem least_budget {c : Colour} {s : State} (win : Win c s) :
    ∃ n, Within c n s ∧ ∀ m, Within c m s → n ≤ m := by
  obtain ⟨n,certificate⟩ := win
  have least : ∀ n, Within c n s → ∃ k, Within c k s ∧ ∀ m, Within c m s → k ≤ m := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro cert
      classical
      by_cases smaller : ∃ k, k < n ∧ Within c k s
      · obtain ⟨k,lt,hk⟩ := smaller; exact ih k lt hk
      · exact ⟨n,cert,fun m hm => by
          by_cases le : n ≤ m
          · exact le
          · exact False.elim (smaller ⟨m,by omega,hm⟩)⟩
  exact least n certificate

private noncomputable def rank (c : Colour) (s : State) : Nat := by
  classical
  exact if win : Win c s then Classical.choose (least_budget win) else 0

private theorem rank_spec {c : Colour} {s : State} (win : Win c s) :
    Within c (rank c s) s ∧ ∀ m, Within c m s → rank c s ≤ m := by
  classical
  simp only [rank,dite_eq_left win]
  exact Classical.choose_spec (least_budget win)

private def Descend (c : Colour) (s t : State) : Prop :=
  BoardStep s t ∧ Win c t ∧ rank c t < rank c s

private theorem progress {c : Colour} {s : State} (win : Win c s)
    (notGoal : ¬ MateGoal c s.board) :
    Ongoing s ∧ (s.board.turn = c → ∃ t, Descend c s t) ∧
      (s.board.turn = c.opp → ¬ CanClaim s ∧ (∃ t, BoardStep s t) ∧
        ∀ t, BoardStep s t → Descend c s t) := by
  have spec := (rank_spec win).1
  have positive : 0 < rank c s := by
    by_cases zero : rank c s = 0
    · rw [zero] at spec; exact False.elim (notGoal spec)
    · omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rank c s ≠ 0)
  rw [hn] at spec
  rcases spec with goal | ⟨ongoing,strong | weak⟩
  · exact False.elim (notGoal goal)
  · obtain ⟨turn,t,step,cert⟩ := strong
    have child : Win c t := ⟨n,cert⟩
    have bound := (rank_spec child).2 n cert
    exact ⟨ongoing,fun _ => ⟨t,step,child,by omega⟩,
      fun wrong => False.elim (opp_ne c (turn.symm.trans wrong))⟩
  · obtain ⟨turn,noClaim,moves,all⟩ := weak
    refine ⟨ongoing,fun wrong => False.elim (opp_ne c (wrong.symm.trans turn)),fun _ => ⟨noClaim,moves,?_⟩⟩
    intro t step
    have child : Win c t := ⟨n,all t step⟩
    have bound := (rank_spec child).2 n (all t step)
    exact ⟨step,child,by omega⟩

private noncomputable def winningPolicy (c : Colour) : Policy := by
  classical
  exact fun s => if h : ∃ t, Descend c s t then some (Classical.choose h) else defaultPolicy s

private theorem winning_legal (c : Colour) : LegalPolicy c (winningPolicy c) := by
  classical
  intro s ongoing turn
  by_cases existsChild : ∃ t, Descend c s t
  · simp only [winningPolicy,dite_eq_left existsChild]
    exact (Classical.choose_spec existsChild).1
  · simp only [winningPolicy,dite_eq_right existsChild]
    exact default_legal c s ongoing turn

private theorem path_descent {c : Colour} {n : Nat} {s t : State}
    (path : PolicyPath c (winningPolicy c) n s t) (win : Win c s) :
    Win c t ∧ rank c t+n ≤ rank c s := by
  classical
  induction path with
  | refl => exact ⟨win,by omega⟩
  | @cons n s u t step own rest ih =>
    have notGoal : ¬ MateGoal c s.board := fun goal => goal.2.2 step.1.2.1
    have prog := progress win notGoal
    have child : Descend c s u := by
      rcases colour_cases c s.board.turn with turn | turn
      · have existsChild := prog.2.1 turn
        have chosen := own turn
        simp only [winningPolicy,dite_eq_left existsChild,Option.some.injEq] at chosen
        rw [← chosen]
        exact Classical.choose_spec existsChild
      · exact (prog.2.2 turn).2.2 u step
    obtain ⟨endWin,bound⟩ := ih child.2.1
    exact ⟨endWin,by have lt := child.2.2; omega⟩

theorem actual_win_of_rule {c : Colour} {s : State} (win : Win c s) : ActualWin c s := by
  classical
  refine ⟨winningPolicy c,rank c s,winning_legal c,?_,?_⟩
  · intro n t path
    have endWin := (path_descent path win).1
    constructor
    · intro stopped
      by_cases goal : MateGoal c t.board
      · exact goal
      · exact False.elim (stopped (progress endWin goal).1)
    · intro ongoing
      have notGoal : ¬ MateGoal c t.board := fun goal => goal.2.2 ongoing.2.1
      have prog := progress endWin notGoal
      constructor
      · intro turn
        have existsChild := prog.2.1 turn
        simp only [winningPolicy,dite_eq_left existsChild]
        intro impossible
        cases impossible
      · exact fun turn => (prog.2.2 turn).1
  · intro n t path
    have bound := (path_descent path win).2
    omega

private theorem policy_certificate {c : Colour} {π : Policy} (legal : LegalPolicy c π)
    (B : Nat) (s : State) (safe : WinningSafety c π s)
    (bound : ∀ n t, PolicyPath c π n s t → n ≤ B) : Within c B s := by
  have successor : ∀ s, WinningSafety c π s → Ongoing s →
      ∃ t, BoardStep s t ∧ (s.board.turn = c → π s = some t) := by
    intro root safety ongoing
    rcases colour_cases c root.board.turn with own | other
    · have notNone := ((safety 0 root (.refl root)).2 ongoing).1 own
      have allowed := legal root ongoing own
      cases value : π root with
      | none => exact False.elim (notNone value)
      | some t => exact ⟨t,by rwa [value] at allowed,fun _ => rfl⟩
    · obtain ⟨r,hr⟩ := ongoing.2.1
      obtain ⟨t,step,_⟩ := layer.reply_complete ongoing hr
      exact ⟨t,step,fun wrong => False.elim (opp_ne c (wrong.symm.trans other))⟩
  induction B generalizing s with
  | zero =>
    by_cases ongoing : Ongoing s
    · obtain ⟨t,step,choice⟩ := successor s safe ongoing
      have impossible := bound 1 t (.cons step choice (.refl t))
      omega
    · exact (safe 0 s (.refl s)).1 ongoing
  | succ B ih =>
    by_cases ongoing : Ongoing s
    · have childSafety : ∀ t, BoardStep s t → (s.board.turn = c → π s = some t) → WinningSafety c π t := by
        intro t step choice n u path
        exact safe (n+1) u (.cons step choice path)
      have childBound : ∀ t, BoardStep s t → (s.board.turn = c → π s = some t) →
          ∀ n u, PolicyPath c π n t u → n ≤ B := by
        intro t step choice n u path
        have old := bound (n+1) u (.cons step choice path)
        omega
      rcases colour_cases c s.board.turn with own | other
      · obtain ⟨t,step,choice⟩ := successor s safe ongoing
        exact Or.inr ⟨ongoing,Or.inl ⟨own,t,step,ih t (childSafety t step choice) (childBound t step choice)⟩⟩
      · obtain ⟨t,step,_⟩ := successor s safe ongoing
        refine Or.inr ⟨ongoing,Or.inr ⟨other,((safe 0 s (.refl s)).2 ongoing).2 other,⟨t,step⟩,?_⟩⟩
        intro u actual
        have choice : s.board.turn = c → π s = some u :=
          fun wrong => False.elim (opp_ne c (wrong.symm.trans other))
        exact ih u (childSafety u actual choice) (childBound u actual choice)
    · exact Or.inl ((safe 0 s (.refl s)).1 ongoing)

theorem actual_win_iff_rule {c : Colour} {s : State} : ActualWin c s ↔ Win c s := by
  constructor
  · rintro ⟨π,B,legal,safe,bound⟩
    exact ⟨B,policy_certificate legal B s safe bound⟩
  · exact actual_win_of_rule

end EndgameChess.Rules.FreshGame
