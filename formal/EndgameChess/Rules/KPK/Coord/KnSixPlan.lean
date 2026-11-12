import EndgameChess.Rules.KPK.Coord.KnSixWin
import EndgameChess.Rules.KPK.Coord.FivePlan

/-! The sixth and seventh ranks of every non-rook pawn are classified, knight pawns
included: outside the guards the pawn owner wins. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- On the knight file the region of `KnSix` is the one used by the winning plan. -/
theorem s5n_iff {a b e f : Nat} : S5n a b e f ↔ Kn.S5 a b 1 e f := by
  constructor
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h1, h2, h3⟩
  · rintro (h | ⟨-, h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩

/-- The winning plan on the sixth and seventh ranks for every non-rook pawn. -/
def knSixPlan : Plan where
  S j a b c d e f := sevkPlan.S j a b c d e f ∨
    (d = 5 ∧ 1 ≤ c ∧ j ≤ 10 ∧ ¬ Kn.S5 a b c e f ∧ Phi j a b c)
  W j a b c d e f := sevkPlan.W j a b c d e f ∨
    (d = 5 ∧ 1 ≤ c ∧ j ≤ 10 ∧ Kn.W5win j a b c e f)
  S_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact sevkPlan.S_le h
    · have := h.2.2.1
      omega
  W_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact sevkPlan.W_le h
    · have := h.2.2.1
      omega
  strong := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, n, ph⟩
    · rcases sevkPlan.strong D h with q | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (strongPush_mono (fun _ _ _ _ _ _ _ w => Or.inl w) q)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inl w⟩
    · rcases Kn.six_move D hc n ph (fun sq k bs u => Kn.step5_cover D hc n sq k bs u) with
        ⟨fr, w⟩ | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (Or.inl ⟨fr, by omega, 2, by omega,
          Or.inl ⟨hc, Nat.le_refl 2, rfl, Or.inr ⟨rfl, w⟩⟩⟩)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inr ⟨rfl, hc, by omega, w⟩⟩
  weak := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, ph, keep, reply, all⟩
    · obtain ⟨q1, q2, q3⟩ := sevkPlan.weak D h
      refine ⟨q1, q2, fun x y st => ?_⟩
      obtain ⟨i, le, s⟩ := q3 x y st
      exact ⟨i, le, Or.inl s⟩
    · exact ⟨keep, reply, fun x y st =>
        ⟨j, Nat.le_refl j, Or.inr ⟨rfl, hc, hj, all x y st, ph⟩⟩⟩

/-- Any non-rook pawn on the sixth rank, pawn owner to move, outside the guard: an actual
win. On the knight file the guard includes the two corner draws. -/
theorem fresh_sixth_win_k {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 5)
    (out : ¬ Kn.S5 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : Dom (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    dom_of_cfg cfg
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  refine fresh_plan_strong (P := knSixPlan) (j := 10) h fresh turn safe
    (Or.inr ⟨rank, file, Nat.le_refl 10, out, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩)))⟩)
  unfold Ch
  omega

/-- Sixth rank, lone king to move, any non-rook pawn: if it cannot take the pawn, has a
move, and no move reaches the guard, the pawn owner wins. -/
theorem fresh_sixth_weak_win_k {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 1 ≤ mx ps ps) (rank : height σ ps = 5)
    (keep : ¬ Capture (mx ps sk) (height σ sk) (mx ps ps) 5 (mx ps wk) (height σ wk))
    (moves : ∃ x y, WeakStep (mx ps sk) (height σ sk) (mx ps ps) 5 (mx ps wk) (height σ wk) x y)
    (all : ∀ x y, WeakStep (mx ps sk) (height σ sk) (mx ps ps) 5 (mx ps wk) (height σ wk) x y →
      ¬ Kn.S5 (mx ps sk) (height σ sk) (mx ps ps) x y) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : Dom (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    dom_of_cfg cfg
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  refine fresh_plan_weak (P := knSixPlan) (j := 10) h fresh turn
    (Or.inr ⟨rank, file, Nat.le_refl 10, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))),
      keep, moves, all⟩)
  unfold Ch
  omega

/-- Knight pawn on the sixth rank, lone king to move: it takes the pawn, is stalemated, or
steps into the guard, and holds. -/
theorem fresh_kn_six_weak_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : mx ps ps = 1) (rank : height σ ps = 5)
    (w : W5n (mx ps sk) (height σ sk) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_weak (G := knSixGuard) h fresh turn (Or.inr ⟨rank, file, w⟩)

end EndgameChess.Rules.KPK.Coord
