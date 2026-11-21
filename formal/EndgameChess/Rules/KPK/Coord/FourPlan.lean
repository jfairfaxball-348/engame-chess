import EndgameChess.Rules.KPK.Coord.FourFront

/-! The fourth-rank winning classes together: the race to a key square, the face-off, the
race for the opposition on the front squares, and the two pawn advances. One plan carries
all of them on top of the fifth-rank plan. -/
namespace EndgameChess.Rules.KPK.Coord

/-- Fourth-rank positions in a winning class, with phase at most `j`. -/
def P3 (j a b c e f : Nat) : Prop :=
  K3 j a b c e f ∨ Face j a b c e f ∨ (∃ p m, m + 10 ≤ j ∧ Front3 m a b c e f p) ∨
    Side3 a b c e f ∨ (f ≤ 2 ∧ ¬ (a = c ∧ b = 4))

/-- The lone king to move after a king step of the plan. -/
def P3W (i x y c e f : Nat) : Prop :=
  (¬ Capture x y c 3 e f ∧ (∃ X Y, WeakStep x y c 3 e f X Y) ∧
      ∀ X Y, WeakStep x y c 3 e f X Y → P3 i x y c X Y) ∨ FaceW i x y c e f

theorem p3_of_k3 {i x y c X Y : Nat} (h : K3 i x y c X Y) : P3 i x y c X Y := Or.inl h

/-- The move of a race or face-off position. -/
theorem kf_move {j a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : K3 j a b c e f ∨ Face j a b c e f) :
    PushOK3 a b c e f ∨ ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 3 e f x y ∧ P3W i x y c e f := by
  rcases h with h | h
  · rcases k3_move D hc h with q | ⟨i, rfl, x, y, st, nc, rep, all⟩
    · exact Or.inl q
    · exact Or.inr ⟨i, rfl, x, y, st, Or.inl ⟨nc, rep, fun X Y w => p3_of_k3 (all X Y w)⟩⟩
  · obtain ⟨i, rfl, x, y, st, w⟩ := face_step D h
    exact Or.inr ⟨i, rfl, x, y, st, Or.inr w⟩

/-- Every position of the classes has its move: a winning push, or a king step after which
every reply is again in the classes with a smaller phase. -/
theorem p3_move {j a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : P3 j a b c e f) :
    PushOK3 a b c e f ∨ ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 3 e f x y ∧ P3W i x y c e f := by
  rcases h with h | h | ⟨p, m, hm, fr⟩ | h | h
  · exact kf_move D hc (Or.inl h)
  · exact kf_move D hc (Or.inr h)
  · rcases front_move D hc fr with q | ⟨q, k⟩ | q | ⟨q, n, hn, k⟩ | ⟨m1, x, y, st, nc, all⟩
    · exact Or.inl q
    · exact kf_move D hc (Or.inl (Or.inr (Or.inr ⟨q, 1, by omega, k⟩)))
    · exact kf_move D hc (Or.inr (face_mono (by omega) q))
    · exact kf_move D hc (Or.inl (Or.inr (Or.inr ⟨q, n, by omega, k⟩)))
    · refine Or.inr ⟨j - 1, by omega, x, y, st, Or.inl ⟨nc,
        weak_reply (dom_step3 D st) (Or.inr (Or.inl (by omega))) nc, fun X Y w => ?_⟩⟩
      rcases all X Y w with q | q
      · exact Or.inr (Or.inr (Or.inl ⟨p, m - 1, by omega, q⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr q)))
  · exact Or.inl (side_push D hc h)
  · exact Or.inl (low_push h.1 h.2)

/-- The lone king's replies. -/
theorem p3w_weak {i x y c e f : Nat} (D : Dom x y c 3 e f) (hc : 1 ≤ c) (h : P3W i x y c e f) :
    ¬ Capture x y c 3 e f ∧ (∃ X Y, WeakStep x y c 3 e f X Y) ∧
      ∀ X Y, WeakStep x y c 3 e f X Y → P3 i x y c X Y := by
  rcases h with h | w
  · exact h
  · have keep := facew_keep w
    refine ⟨keep, weak_reply D (Or.inr (Or.inl (by omega))) keep, fun X Y st => ?_⟩
    rcases facew_reply hc w st with ⟨p, m, hm, k⟩ | q
    · exact Or.inl (Or.inr (Or.inr ⟨p, m, hm, k⟩))
    · exact Or.inr (Or.inl q)

/-- The fourth-rank winning classes on top of the fifth-rank plan. -/
def fourPlan : Plan where
  S j a b c d e f := knFivePlan.S j a b c d e f ∨ (d = 3 ∧ 1 ≤ c ∧ j ≤ 30 ∧ P3 j a b c e f)
  W j a b c d e f := knFivePlan.W j a b c d e f ∨ (d = 3 ∧ 1 ≤ c ∧ j ≤ 30 ∧ P3W j a b c e f)
  S_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact knFivePlan.S_le h
    · have := h.2.2.1
      omega
  W_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact knFivePlan.W_le h
    · have := h.2.2.1
      omega
  strong := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, k⟩
    · rcases knFivePlan.strong D h with q | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (strongPush_mono (fun _ _ _ _ _ _ _ w => Or.inl w) q)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inl w⟩
    · rcases p3_move D hc k with ⟨fr, lost⟩ | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (Or.inl ⟨fr, by omega, 13, by omega,
          Or.inl (Or.inr ⟨rfl, hc, Nat.le_refl 13, lost4_w4win (dom_push3 D fr) hc lost⟩)⟩)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inr ⟨rfl, hc, by omega, w⟩⟩
  weak := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, w⟩
    · obtain ⟨q1, q2, q3⟩ := knFivePlan.weak D h
      refine ⟨q1, q2, fun x y st => ?_⟩
      obtain ⟨i, le, s⟩ := q3 x y st
      exact ⟨i, le, Or.inl s⟩
    · obtain ⟨keep, rep, all⟩ := p3w_weak D hc w
      exact ⟨keep, rep, fun x y st => ⟨j, Nat.le_refl j, Or.inr ⟨rfl, hc, hj, all x y st⟩⟩⟩

open EndgameChess.KK in
/-- Fourth rank, pawn owner to move, any non-rook pawn: a root in one of the winning
classes with phase at most 30 is an actual win. -/
theorem fresh_four_p3_win {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (k : P3 30 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_plan_strong (P := fourPlan) (j := 30) h fresh turn safe
    (Or.inr ⟨rank, file, Nat.le_refl 30, k⟩)

open EndgameChess.KK in
/-- Fourth rank, pawn owner to move: if the king reaches a front square before the lone
king reaches the square two above it, the pawn being safe on the way and the king not
having to pass in front of the lone king or through the pawn, the pawn owner wins. -/
theorem fresh_four_front_win {σ : Colour} {q : Position} {sk ps wk : Square} {m p : Nat}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (k : Front3 m (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk) p) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  rw [rank] at D
  have hm := front_le D k
  exact fresh_four_p3_win h fresh turn safe file rank
    (Or.inr (Or.inr (Or.inl ⟨p, m, by omega, k⟩)))

end EndgameChess.Rules.KPK.Coord
