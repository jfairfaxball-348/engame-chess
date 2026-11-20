import EndgameChess.Rules.KPK.Coord.KnSixPlan

/-! The fifth rank of every non-rook pawn, knight pawns included. The guard region `S4`
and the winning phases `Ph4` are those of the bishop and centre pawns; on the knight file
they sit on the knight sixth-rank guard and plan. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- Knight pawn on the fifth, sixth or seventh rank. -/
def knFiveGuard : Guard where
  S a b c d e f := knSixGuard.S a b c d e f ∨ (d = 4 ∧ c = 1 ∧ S4 a b 1 e f)
  W a b c d e f := knSixGuard.W a b c d e f ∨ (d = 4 ∧ c = 1 ∧ W4 a b 1 e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | ⟨rfl, rfl, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := knSixGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r),
        fun p r t => Or.inl (q3 p r t), q4⟩
    · exact ⟨fun x y st => Or.inr ⟨rfl, rfl, s4_king D (Nat.le_refl 1) h st⟩,
        fun fr _ => Or.inl (Or.inr ⟨rfl, rfl, w5n_of (s4_push D (Nat.le_refl 1) h fr)⟩),
        fun q => by omega, fun q => by omega⟩
  weak := by
    intro a b c d e f D h
    rcases h with h | ⟨rfl, rfl, h⟩
    · rcases knSixGuard.weak D h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inl q⟩)
    · rcases h with q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr ⟨rfl, rfl, q⟩⟩)

/-- Knight pawn on the fifth, sixth or seventh rank, a fresh root in the guard with the
pawn owner to move: the lone king holds. -/
theorem fresh_kn_five_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (sat : SD knFiveGuard σ sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong h fresh turn safe sat

/-- Knight pawn on the fifth rank, lone king to move: it takes the pawn or steps into the
guard, and holds. -/
theorem fresh_kn_five_weak_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : mx ps ps = 1) (rank : height σ ps = 4)
    (w : W4 (mx ps sk) (height σ sk) 1 (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_weak (G := knFiveGuard) h fresh turn (Or.inr ⟨rank, file, w⟩)

/-- The winning plan on the fifth, sixth and seventh ranks for every non-rook pawn. -/
def knFivePlan : Plan where
  S j a b c d e f := knSixPlan.S j a b c d e f ∨
    (d = 4 ∧ 1 ≤ c ∧ j ≤ 13 ∧ ¬ S4 a b c e f ∧ Ph4 j a b c e f)
  W j a b c d e f := knSixPlan.W j a b c d e f ∨
    (d = 4 ∧ 1 ≤ c ∧ j ≤ 13 ∧ W4win j a b c e f)
  S_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact knSixPlan.S_le h
    · have := h.2.2.1
      omega
  W_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact knSixPlan.W_le h
    · have := h.2.2.1
      omega
  strong := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, out, ph⟩
    · rcases knSixPlan.strong D h with q | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (strongPush_mono (fun _ _ _ _ _ _ _ w => Or.inl w) q)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inl w⟩
    · rcases mv4 D hc out ph with ⟨fr, w5⟩ | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (Or.inl ⟨fr, by omega, 10, by omega,
          Or.inl (Or.inr ⟨rfl, hc, Nat.le_refl 10, w5⟩)⟩)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inr ⟨rfl, hc, by omega, w⟩⟩
  weak := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, keep, reply, all⟩
    · obtain ⟨q1, q2, q3⟩ := knSixPlan.weak D h
      refine ⟨q1, q2, fun x y st => ?_⟩
      obtain ⟨i, le, s⟩ := q3 x y st
      exact ⟨i, le, Or.inl s⟩
    · exact ⟨keep, reply, fun x y st =>
        ⟨j, Nat.le_refl j, Or.inr ⟨rfl, hc, hj, (all x y st).1, (all x y st).2⟩⟩⟩

/-- Any non-rook pawn on the fifth rank, pawn owner to move, outside the guard: an actual
win. With `fresh_kn_five_hold` this classifies the knight-pawn roots. -/
theorem fresh_fifth_win_k {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 4)
    (out : ¬ S4 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  rw [rank] at D
  exact fresh_plan_strong (P := knFivePlan) (j := 13) h fresh turn safe
    (Or.inr ⟨rank, file, Nat.le_refl 13, out, five_cover D file out⟩)

/-- Fifth rank, lone king to move, any non-rook pawn: if it cannot take the pawn and no
move reaches the guard, the pawn owner wins. -/
theorem fresh_fifth_weak_win_k {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 1 ≤ mx ps ps) (rank : height σ ps = 4)
    (keep : ¬ Capture (mx ps sk) (height σ sk) (mx ps ps) 4 (mx ps wk) (height σ wk))
    (all : ∀ x y, WeakStep (mx ps sk) (height σ sk) (mx ps ps) 4 (mx ps wk) (height σ wk) x y →
      ¬ S4 (mx ps sk) (height σ sk) (mx ps ps) x y) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : Dom (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    dom_of_cfg cfg
  rw [rank] at D
  exact fresh_plan_weak (P := knFivePlan) (j := 13) h fresh turn
    (Or.inr ⟨rank, file, Nat.le_refl 13, keep,
      weak_reply D (Or.inr (Or.inl (Nat.le_refl 4))) keep,
      fun x y st => ⟨all x y st, five_cover (domS_reply D st) file (all x y st)⟩⟩)

end EndgameChess.Rules.KPK.Coord
