import EndgameChess.Rules.KPK.Coord.SixPlan

/-! The seventh rank for every non-rook pawn, knight pawns included: outside the top guard
the pawn owner wins. The argument is that of `SevenWin`, stated with a side predicate
that does not mention a file two out, which a knight pawn lacks on one side. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- `t` is a file next to the pawn and `o` the other one. -/
def Sd1 (c t o : Nat) : Prop := (t = c + 1 ∧ o + 1 = c) ∨ (t + 1 = c ∧ o = c + 1)

/-- The lone king beside the pawn, the strong king one step from the far side. -/
def Far7k (a b c e f : Nat) : Prop :=
  ∃ t o, Sd1 c t o ∧ e = t ∧ f = 6 ∧ (Within1 a b o 6 ∨ Within1 a b o 7)

/-- Knight pawn, lone king in the far corner on the pawn's side, king two ranks above it:
a promoted rook or queen would stalemate. -/
def Trap7 (a b c e f : Nat) : Prop := c = 1 ∧ e = 0 ∧ f = 0 ∧ a ≤ 1 ∧ b = 2

def SevSk (j a b c e f : Nat) : Prop :=
  (Prom a b c e f ∧ ¬ Trap7 a b c e f) ∨ (a = c ∧ b = 7 ∧ 1 ≤ j) ∨ (Far7k a b c e f ∧ 1 ≤ j) ∨
    (Evict a b c e f ∧ 2 ≤ j) ∨ (Trap7 a b c e f ∧ 1 ≤ j)

/-- Lone king to move: the king supports promotion, or it evicts, or it has stepped out
of the corner trap. -/
def SevWk (j a b c e f : Nat) : Prop :=
  R6 a b c 6 ∨ (∃ t o, Sd1 c t o ∧ a = t ∧ b = 5 ∧ e = c ∧ f = 7 ∧ 1 ≤ j) ∨
    (c = 1 ∧ e = 0 ∧ f = 0 ∧ b = 2 ∧ (a = 1 ∨ a = 2))

theorem rook_of_prom_k {a b c e f : Nat} (D : DomS a b c 6 e f) (h : Prom a b c e f)
    (nt : ¬ Trap7 a b c e f) : RookGood a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  obtain ⟨fr, h⟩ := h
  unfold Free at fr
  by_cases near : Near a b c 7
  · apply r6_good D
    unfold Near at near
    unfold R6
    omega
  · have nw : ¬ Near e f c 7 := by
      rcases h with h | h
      · exact h
      · exact absurd h near
    unfold Near at nw
    unfold Trap7 at nt
    exact run_rook u1 u2 u3 u6 u7 k1 (by unfold Outside; omega) nt

set_option maxHeartbeats 4000000 in
/-- Pawn on the seventh: the winning moves. -/
theorem sevk_strong {W : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop} {j a b c e f : Nat}
    (D : DomS a b c 6 e f) (hc : 1 ≤ c) (hj : j ≤ 2) (h : SevSk j a b c e f) :
    StrongPush W a b c 6 e f ∨
      ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 6 e f x y ∧ SevWk i x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  have k3 := D.1.k3
  by_cases tr : Trap7 a b c e f
  · unfold Trap7 at tr
    obtain ⟨rfl, rfl, rfl, ha, rfl⟩ := tr
    have one : 1 ≤ j := by
      rcases h with ⟨-, nt⟩ | ⟨-, -, o⟩ | ⟨-, o⟩ | ⟨-, o⟩ | ⟨-, o⟩
      · exact (nt ⟨rfl, rfl, rfl, ha, rfl⟩).elim
      all_goals omega
    exact Or.inr ⟨j - 1, by omega, a + 1, 2, by unfold KingStep Near Apart; omega,
      Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, by omega⟩)⟩
  by_cases pr : Prom a b c e f
  · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, pr.1, rook_of_prom_k D pr tr⟩)))
  have pr' := pr
  unfold Prom Free Near at pr'
  rcases h with h | ⟨rfl, rfl, one⟩ | ⟨⟨t, o, sd, rfl, rfl, w⟩, one⟩ | ⟨⟨rfl, rfl, w⟩, two⟩ | ⟨t, -⟩
  rotate_right
  · exact absurd t tr
  · exact absurd h.1 pr
  · refine Or.inr ⟨j - 1, by omega, ?_⟩
    by_cases g : Apart (a + 1) 7 e f
    · exact ⟨a + 1, 7, by unfold Apart at g; unfold KingStep Near Apart; omega,
        Or.inl (by unfold R6; omega)⟩
    · unfold Apart at g
      exact ⟨a - 1, 7, by unfold KingStep Near Apart; omega, Or.inl (by unfold R6; omega)⟩
  · unfold Sd1 at sd
    unfold Within1 at w
    refine Or.inr ⟨j - 1, by omega, ?_⟩
    by_cases g : a = o ∧ b = 6
    · omega
    by_cases g7 : Within1 a b o 6
    · unfold Within1 at g7
      exact ⟨o, 6, by unfold KingStep Near Apart; omega, Or.inl (by unfold R6; omega)⟩
    · unfold Within1 at g7
      exact ⟨o, 7, by unfold KingStep Near Apart; omega, Or.inl (by unfold R6; omega)⟩
  · refine Or.inr ⟨j - 1, by omega, ?_⟩
    by_cases g : Near a b (e + 1) 5
    · unfold Near at g
      exact ⟨e + 1, 5, by unfold KingStep Near Apart; omega,
        Or.inr (Or.inl ⟨e + 1, e - 1, Or.inl ⟨rfl, by omega⟩, rfl, rfl, rfl, rfl, by omega⟩)⟩
    · have g' : Near a b (e - 1) 5 := by
        rcases w with w | w
        · exact absurd w g
        · exact w
      unfold Near at g'
      exact ⟨e - 1, 5, by unfold KingStep Near Apart; omega,
        Or.inr (Or.inl ⟨e - 1, e + 1, Or.inr ⟨by omega, rfl⟩, rfl, rfl, rfl, rfl, by omega⟩)⟩

set_option maxHeartbeats 4000000 in
/-- Pawn on the seventh: every reply stays winning. -/
theorem sevk_weak {j a b c e f : Nat} (D : Dom a b c 6 e f) (hc : 1 ≤ c)
    (h : SevWk j a b c e f) :
    ¬ Capture a b c 6 e f ∧ (∃ x y, WeakStep a b c 6 e f x y) ∧
      ∀ x y, WeakStep a b c 6 e f x y → SevSk j a b c x y := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  rcases h with h | ⟨t, o, sd, ha, rfl, he, rfl, one⟩ | ⟨rfl, rfl, rfl, rfl, ha⟩
  rotate_right
  · have keep : ¬ Capture a 2 1 6 0 0 := by unfold Capture Near; omega
    refine ⟨keep, ⟨1, 0, by unfold WeakStep Near Apart Att; omega⟩, ?_⟩
    intro x y st
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
    have a5 := st.k5
    refine Or.inl ⟨⟨by unfold Free; omega, Or.inl (by unfold Near; omega)⟩, ?_⟩
    unfold Trap7
    omega
  · have h' := h
    unfold R6 at h'
    have keep : ¬ Capture a b c 6 e f := by unfold Capture Near; omega
    refine ⟨keep, key_reply D hc keep (Or.inr h), ?_⟩
    intro x y st
    have k7 := st.k7
    have k5 := st.k6
    refine Or.inl ⟨⟨?_, Or.inr (by unfold Near; omega)⟩, by unfold Trap7; omega⟩
    unfold Free
    omega
  · have sw : Sd1 c o t := by
      unfold Sd1 at sd ⊢
      omega
    have sd' := sd
    unfold Sd1 at sd'
    have keep : ¬ Capture a 5 c 6 e 7 := by unfold Capture Near; omega
    refine ⟨keep, ⟨o, 6, by unfold WeakStep Near Apart Att; omega⟩, ?_⟩
    intro x y st
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
    have a5 := st.k5
    have a6 := st.k6
    have a7 := st.k7
    have a8 := st.k8
    have hx : x = o ∧ y = 6 := by omega
    obtain ⟨rfl, rfl⟩ := hx
    exact Or.inr (Or.inr (Or.inl ⟨⟨x, t, sw, rfl, rfl, Or.inl (by unfold Within1; omega)⟩, one⟩))

set_option maxHeartbeats 4000000 in
/-- Outside the top guard the pawn on the seventh wins. -/
theorem sevk_cover {a b c e f : Nat} (D : DomS a b c 6 e f) (hc : 1 ≤ c)
    (n : ¬ TS a b c 6 e f) : SevSk 2 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k3 := D.1.k3
  have k4 := D.k4
  by_cases tr : Trap7 a b c e f
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨tr, by omega⟩)))
  by_cases pr : Prom a b c e f
  · exact Or.inl ⟨pr, tr⟩
  have pr' := pr
  unfold Prom Free at pr'
  by_cases top : a = c ∧ b = 7
  · exact Or.inr (Or.inl ⟨top.1, top.2, by omega⟩)
  have ntop : ¬ (a = c ∧ b = 7) := top
  by_cases block : e = c ∧ f = 7
  · obtain ⟨rfl, rfl⟩ := block
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl, ?_⟩, by omega⟩)))
    apply Classical.byContradiction
    intro q
    exact n ⟨hc, rfl, Or.inl ⟨rfl, rfl, fun g => q (Or.inl g), fun g => q (Or.inr g.2)⟩⟩
  have w : Near e f c 7 := by
    by_cases g : Near e f c 7
    · exact g
    · exfalso; apply pr; exact ⟨by unfold Free; omega, Or.inl g⟩
  unfold Near at w
  have row : f = 6 := by omega
  subst row
  by_cases g : e + 1 = c
  · refine Or.inr (Or.inr (Or.inl ⟨⟨c - 1, c + 1, Or.inr ⟨by omega, rfl⟩, by omega, rfl, ?_⟩,
      by omega⟩))
    apply Classical.byContradiction
    intro q
    exact n ⟨hc, rfl, Or.inr (Or.inl ⟨g, rfl, fun z => q (Or.inl z), fun z => q (Or.inr z)⟩)⟩
  · have g2 : e = c + 1 := by omega
    refine Or.inr (Or.inr (Or.inl ⟨⟨c + 1, c - 1, Or.inl ⟨rfl, by omega⟩, g2, rfl, ?_⟩,
      by omega⟩))
    apply Classical.byContradiction
    intro q
    exact n ⟨hc, rfl, Or.inr (Or.inr ⟨g2, rfl, fun z => q (Or.inl z), fun z => q (Or.inr z)⟩)⟩

/-- The winning plan with any non-rook pawn on the seventh rank, both turns. -/
def sevkPlan : Plan where
  S j a b c d e f := 1 ≤ c ∧ j ≤ 2 ∧ d = 6 ∧ SevSk j a b c e f
  W j a b c d e f := 1 ≤ c ∧ j ≤ 2 ∧ d = 6 ∧ (SevWk j a b c e f ∨ (j = 2 ∧ W6 a b c e f))
  S_le := fun h => by have := h.2.1; omega
  W_le := fun h => by have := h.2.1; omega
  strong := by
    intro j a b c d e f D h
    obtain ⟨hc, hj, rfl, h⟩ := h
    rcases sevk_strong D hc hj h with q | ⟨i, rfl, x, y, st, w⟩
    · exact Or.inl q
    · exact Or.inr ⟨i, rfl, x, y, st, hc, by omega, rfl, Or.inl w⟩
  weak := by
    intro j a b c d e f D h
    obtain ⟨hc, hj, rfl, h | ⟨rfl, q1, q2, q3⟩⟩ := h
    · obtain ⟨q1, q2, q3⟩ := sevk_weak D hc h
      exact ⟨q1, q2, fun x y st => ⟨j, Nat.le_refl j, hc, hj, rfl, q3 x y st⟩⟩
    · exact ⟨q1, q2, fun x y st => ⟨2, Nat.le_refl 2, hc, hj, rfl,
        sevk_cover (domS_of_step D st) hc (q3 x y st)⟩⟩

/-- Any non-rook pawn on the seventh rank, pawn owner to move, outside the top guard: an
actual win. With `fresh_top_hold` this classifies these roots, knight pawns included. -/
theorem fresh_seventh_win_k {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (top : height σ ps = 6)
    (out : ¬ TS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  rw [top] at D out
  have cov := sevk_cover D file out
  exact fresh_plan_strong (P := sevkPlan) (j := 2) h fresh turn safe ⟨file, by omega, top, cov⟩

/-- Seventh rank, lone king to move, any non-rook pawn: if it cannot take the pawn, has a
move, and no move reaches the guard, the pawn owner wins. -/
theorem fresh_seventh_weak_win_k {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 1 ≤ mx ps ps) (rank : height σ ps = 6)
    (w : W6 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_plan_weak (P := sevkPlan) (j := 2) h fresh turn
    ⟨file, by omega, rank, Or.inr ⟨rfl, w⟩⟩

end EndgameChess.Rules.KPK.Coord
