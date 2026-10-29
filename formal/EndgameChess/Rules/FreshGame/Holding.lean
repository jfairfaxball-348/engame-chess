import EndgameChess.Rules.FreshGame.Lifting

namespace EndgameChess.Rules.FreshGame
open EndgameChess.KK

abbrev Policy := State → Option State

def LegalPolicy (c : Colour) (π : Policy) : Prop :=
  ∀ s, Ongoing s → s.board.turn = c →
    match π s with
    | none => CanClaim s
    | some t => BoardStep s t

inductive PolicyPath (c : Colour) (π : Policy) : Nat → State → State → Prop
  | refl (s : State) : PolicyPath c π 0 s s
  | cons {n : Nat} {s u t : State} : BoardStep s u →
      (s.board.turn = c → π s = some u) →
      PolicyPath c π n u t → PolicyPath c π (n+1) s t

/-- An actual legal policy prevents the opponent's mate on every compliant
finite prefix, including terminal endpoints. A claim stops with a draw. -/
def Hold (c : Colour) (s : State) : Prop :=
  ∃ π, LegalPolicy c π ∧ ∀ n t, PolicyPath c π n s t → ¬ MateGoal c.opp t.board

noncomputable def defaultPolicy : Policy := by
  classical
  exact fun s => if h : ∃ t, BoardStep s t then some (Classical.choose h) else none

theorem default_legal (c : Colour) : LegalPolicy c defaultPolicy := by
  classical
  intro s ongoing _
  have existsStep : ∃ t, BoardStep s t := by
    obtain ⟨r,hr⟩ := ongoing.2.1
    obtain ⟨t,actual,_⟩ := layer.reply_complete ongoing hr
    exact ⟨t,actual⟩
  simp only [defaultPolicy,dite_eq_left existsStep]
  exact Classical.choose_spec existsStep

theorem path_reach {c : Colour} {π : Policy} {n : Nat} {s t : State}
    (path : PolicyPath c π n s t) : ReachK s.board t.board := by
  induction path with
  | refl => exact ReachK.refl _
  | cons step _ _ ih => exact reachK_cons (step_legal step) ih

private theorem terminal_path {c : Colour} {π : Policy} {n : Nat} {s t : State}
    (terminal : ¬ Ongoing s) (path : PolicyPath c π n s t) : t = s := by
  cases path with
  | refl => rfl
  | cons step _ _ => exact False.elim (terminal step.1)

theorem terminal_hold {c : Colour} {s : State}
    (terminal : ¬ Ongoing s) (safe : ¬ MateGoal c.opp s.board) : Hold c s := by
  refine ⟨defaultPolicy,default_legal c,?_⟩
  intro n t path
  have equal := terminal_path terminal path
  simpa only [equal] using safe

theorem hold_of_safe_reach {c : Colour} {s : State}
    (safe : ∀ q, ReachK s.board q → ¬ MateGoal c.opp q) : Hold c s :=
  ⟨defaultPolicy,default_legal c,fun _ _ path => safe _ (path_reach path)⟩

/-- A legal move to a dead board is an explicit holding choice. If the
root is already stopped, no move is needed. -/
theorem hold_via_dead_reply {c : Colour} {s : State} (turn : s.board.turn = c)
    (safe : ¬ MateGoal c.opp s.board) (capture : ∃ r, Legal s.board r ∧ DeadK r) : Hold c s := by
  classical
  by_cases ongoing : Ongoing s
  · obtain ⟨r,⟨m,hm,rfl⟩,dead⟩ := capture
    let u := afterMove s m
    have actual : BoardStep s u := ⟨ongoing,m,hm,rfl⟩
    let π : Policy := fun t => if t = s then some u else defaultPolicy t
    have legal : LegalPolicy c π := by
      intro t ho ht
      by_cases same : t = s
      · subst t; simpa only [π,ite_eq_left rfl] using actual
      · simpa only [π,ite_eq_right same] using default_legal c t ho ht
    refine ⟨π,legal,?_⟩
    intro n t path
    cases path with
    | refl => exact safe
    | @cons n _ v _ step own rest =>
      have equal : v = u := by
        have chosen := own turn
        simp only [π,ite_eq_left rfl,Option.some.injEq] at chosen
        exact chosen.symm
      subst v
      have stopped : ¬ Ongoing u := fun ho => ho.1 dead
      have endpoint := terminal_path stopped rest
      subst t
      intro goal
      exact dead ⟨u.board,ReachK.refl _,goal.2⟩
  · exact terminal_hold ongoing safe

/-- A genuine holding policy excludes the opponent's finite forcing tree.
This connects the independent policy semantics to the rule certificates. -/
theorem hold_not_win {c : Colour} {s : State} (holding : Hold c s) : ¬ Win c.opp s := by
  obtain ⟨π,legal,safe⟩ := holding
  rintro ⟨n,win⟩
  have impossible : ∀ n s, Within c.opp n s →
      (∀ k t, PolicyPath c π k s t → ¬ MateGoal c.opp t.board) → False := by
    intro n
    induction n with
    | zero => intro s goal safe; exact safe 0 s (.refl s) goal
    | succ n ih =>
      intro s win safe
      rcases win with goal | ⟨ongoing,strong | weak⟩
      · exact safe 0 s (.refl s) goal
      · obtain ⟨turn,t,step,next⟩ := strong
        apply ih t next
        intro k u path
        exact safe (k+1) u (.cons step (fun wrong => False.elim (opp_ne c (wrong.symm.trans turn))) path)
      · obtain ⟨turn,noClaim,_,all⟩ := weak
        have own : s.board.turn = c := by simpa only [layer,opp_opp] using turn
        have permitted := legal s ongoing own
        cases chosen : π s with
        | none => rw [chosen] at permitted; exact noClaim permitted
        | some t =>
          rw [chosen] at permitted
          apply ih t (all t permitted)
          intro k u path
          exact safe (k+1) u (.cons permitted (fun _ => chosen) path)
  exact impossible n s win safe

end EndgameChess.Rules.FreshGame
