import EndgameChess.Rules.KRKWinning.Definitions
namespace EndgameChess.Rules.KRKWinning
open EndgameChess.KK RawHistoryLayer KRKHolding

/-- ANY actual bounded winning policy yields the SAME B-ply frozen certificate. -/
theorem policy_certificate {c : Colour} {π : Policy} (legal : LegalPolicy c π)
    (B : Nat) (s : State) (safe : WinningSafety c π s)
    (bound : ∀ n t, PolicyPath c π n s t → n ≤ B) : W c B s := by
  classical
  have successor : ∀ s, WinningSafety c π s → Ongoing s →
      ∃ t, BoardStep s t ∧ ((erase s).turn = c → π s = some t) := by
    intro root rootSafe ongoing
    by_cases own : (erase root).turn = c
    · have notNone := ((rootSafe 0 root (.refl root)).2 ongoing).1 own
      have allowed := legal root ongoing own
      cases value : π root with
      | none => exact False.elim (notNone value)
      | some t =>
        have edge : BoardStep root t := by rwa [value] at allowed
        exact ⟨t,edge,fun _ => rfl⟩
    · obtain ⟨r,move⟩ := ((RawAdjudication.ongoing_iff root.val).mp ongoing).2.1
      obtain ⟨t,edge,_⟩ := layer.reply_complete ongoing move
      exact ⟨t,edge,fun bad => False.elim (own bad)⟩
  induction B generalizing s with
  | zero =>
    by_cases ongoing : Ongoing s
    · obtain ⟨t,edge,choice⟩ := successor s safe ongoing
      have impossible := bound 1 t (.cons edge choice (.refl t))
      omega
    · exact (safe 0 s (.refl s)).1 ongoing
  | succ B ih =>
    by_cases ongoing : Ongoing s
    · have childSafety : ∀ t, BoardStep s t → ((erase s).turn = c → π s = some t) →
          WinningSafety c π t := by
        intro t edge choice n u path
        exact safe (n+1) u (.cons edge choice path)
      have childBound : ∀ t, BoardStep s t → ((erase s).turn = c → π s = some t) →
          ∀ n u, PolicyPath c π n t u → n ≤ B := by
        intro t edge choice n u path
        have prior := bound (n+1) u (.cons edge choice path)
        omega
      rcases colour_cases c (erase s).turn with own | opponent
      · obtain ⟨t,edge,choice⟩ := successor s safe ongoing
        have certified := ih t (childSafety t edge choice) (childBound t edge choice)
        exact Or.inr ⟨ongoing,Or.inl ⟨own,t,edge,certified⟩⟩
      · obtain ⟨t,edge,_⟩ := successor s safe ongoing
        have noClaim := ((safe 0 s (.refl s)).2 ongoing).2 opponent
        refine Or.inr ⟨ongoing,Or.inr ⟨opponent,noClaim,⟨t,edge⟩,?_⟩⟩
        intro u move
        have choice : (erase s).turn = c → π s = some u := by
          intro bad
          exact False.elim (opp_ne c (bad.symm.trans opponent))
        exact ih u (childSafety u move choice) (childBound u move choice)
    · exact budget_monotone.1 c s _ ((safe 0 s (.refl s)).1 ongoing)
end EndgameChess.Rules.KRKWinning
