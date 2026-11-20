import EndgameChess.Rules.KPK.Coord.SixPlan

/-! With a bishop or centre pawn on the sixth rank the lone king is never stalemated: if it
cannot take the pawn it has a legal step. So the lone king's turn on the sixth rank is
classified without exception. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

set_option maxHeartbeats 4000000 in
/-- Bishop or centre pawn on the sixth rank: the lone king always has a step unless it
can take the pawn. -/
theorem six_reply_all {a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 2 ≤ c)
    (keep : ¬ Capture a b c 5 e f) : ∃ x y, WeakStep a b c 5 e f x y := by
  by_cases ex : c = 2 ∧ e = 0 ∧ f = 7 ∧ a = 1 ∧ b = 5
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ex
    exact ⟨1, 7, by unfold WeakStep Near Apart Att; omega⟩
  · exact six_reply D hc keep ex

/-- Sixth rank, lone king to move: if it cannot take the pawn and no step reaches the guard,
the pawn owner wins. Unlike `fresh_sixth_weak_win` no reply needs to be assumed. -/
theorem fresh_sixth_weak_win' {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 2 ≤ mx ps ps) (rank : height σ ps = 5)
    (keep : ¬ Capture (mx ps sk) (height σ sk) (mx ps ps) 5 (mx ps wk) (height σ wk))
    (all : ∀ x y, WeakStep (mx ps sk) (height σ sk) (mx ps ps) 5 (mx ps wk) (height σ wk) x y →
      ¬ S5 (mx ps sk) (height σ sk) (mx ps ps) x y) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : Dom (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    dom_of_cfg cfg
  rw [rank] at D
  exact fresh_sixth_weak_win h fresh turn file rank keep (six_reply_all D file keep) all

/-- Sixth rank, lone king to move, bishop or centre pawn: exactly one of the two holds.
The lone king holds if it can take the pawn or step into the guard, and otherwise loses. -/
theorem sixth_weak_cases {a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 2 ≤ c) :
    W5 a b c e f ∨
      (¬ Capture a b c 5 e f ∧ ∀ x y, WeakStep a b c 5 e f x y → ¬ S5 a b c x y) := by
  by_cases cap : Capture a b c 5 e f
  · exact Or.inl (Or.inl cap)
  by_cases st : ∃ x y, WeakStep a b c 5 e f x y ∧ S5 a b c x y
  · exact Or.inl (Or.inr st)
  · exact Or.inr ⟨cap, fun x y s g => st ⟨x, y, s, g⟩⟩

end EndgameChess.Rules.KPK.Coord
