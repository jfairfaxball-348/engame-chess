import EndgameChess.Rules.KPK.Coord.Key
import EndgameChess.Rules.KPK.Coord.Sixth

/-! Wins with a bishop or centre pawn on the seventh rank: exactly the positions outside
the top guard. The pawn promotes, or the king first gets next to the promotion square. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- The promoted piece cannot be taken at once. -/
def Prom (a b c e f : Nat) : Prop := Free a b e f c 7 ∧ (¬ Near e f c 7 ∨ Near a b c 7)

/-- The lone king beside the pawn, the strong king one step from the far side. -/
def Far7 (a b c e f : Nat) : Prop :=
  ∃ t o u, Sd c t o u ∧ e = t ∧ f = 6 ∧ (Within1 a b o 6 ∨ Within1 a b o 7)

/-- The lone king on the promotion square, the strong king able to step beside the
square behind the pawn. -/
def Evict (a b c e f : Nat) : Prop :=
  e = c ∧ f = 7 ∧ (Near a b (c + 1) 5 ∨ Near a b (c - 1) 5)

def SevS (j a b c e f : Nat) : Prop :=
  Prom a b c e f ∨ (a = c ∧ b = 7 ∧ 1 ≤ j) ∨ (Far7 a b c e f ∧ 1 ≤ j) ∨ (Evict a b c e f ∧ 2 ≤ j)

/-- Lone king to move: the king supports promotion, or it evicts. -/
def SevW (j a b c e f : Nat) : Prop :=
  R6 a b c 6 ∨ (∃ t o u, Sd c t o u ∧ a = t ∧ b = 5 ∧ e = c ∧ f = 7 ∧ 1 ≤ j)

theorem rook_of_prom {a b c e f : Nat} (D : DomS a b c 6 e f) (hc : 2 ≤ c) (h : Prom a b c e f) :
    RookGood a b c e f := by
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
    exact run_rook u1 u2 u3 u6 u7 k1 (by unfold Outside; omega) (by omega)

theorem Sd.swap {c t o u : Nat} (hc : 2 ≤ c) (h : Sd c t o u) : ∃ v, Sd c o t v := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨c - 2, Or.inr ⟨h2, h1, by omega⟩⟩
  · exact ⟨c + 2, Or.inl ⟨h2, h1, rfl⟩⟩

/-- Pawn on the seventh: the winning moves. -/
theorem sev_strong {W : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop} {j a b c e f : Nat} (D : DomS a b c 6 e f) (hc : 2 ≤ c) (hj : j ≤ 2)
    (h : SevS j a b c e f) :
    StrongPush W a b c 6 e f ∨
      ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 6 e f x y ∧ SevW i x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  have k3 := D.1.k3
  by_cases pr : Prom a b c e f
  · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, pr.1, rook_of_prom D hc pr⟩)))
  have pr' := pr
  unfold Prom Free Near at pr'
  rcases h with h | ⟨rfl, rfl, one⟩ | ⟨⟨t, o, u, sd, rfl, rfl, w⟩, one⟩ | ⟨⟨rfl, rfl, w⟩, two⟩
  · exact absurd h pr
  · refine Or.inr ⟨j - 1, by omega, ?_⟩
    by_cases g : Apart (a + 1) 7 e f
    · exact ⟨a + 1, 7, by unfold Apart at g; unfold KingStep Near Apart; omega, Or.inl (by unfold R6; omega)⟩
    · unfold Apart at g
      exact ⟨a - 1, 7, by unfold KingStep Near Apart; omega, Or.inl (by unfold R6; omega)⟩
  · unfold Sd at sd
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
        Or.inr ⟨e + 1, e - 1, e + 2, Or.inl ⟨rfl, by omega, rfl⟩, rfl, rfl, rfl, rfl, by omega⟩⟩
    · have g' : Near a b (e - 1) 5 := by
        rcases w with w | w
        · exact absurd w g
        · exact w
      unfold Near at g'
      exact ⟨e - 1, 5, by unfold KingStep Near Apart; omega,
        Or.inr ⟨e - 1, e + 1, e - 2, Or.inr ⟨by omega, rfl, by omega⟩, rfl, rfl, rfl, rfl, by omega⟩⟩

/-- Pawn on the seventh: every reply stays winning. -/
theorem sev_weak {j a b c e f : Nat} (D : Dom a b c 6 e f) (hc : 2 ≤ c) (h : SevW j a b c e f) :
    ¬ Capture a b c 6 e f ∧ (∃ x y, WeakStep a b c 6 e f x y) ∧
      ∀ x y, WeakStep a b c 6 e f x y → SevS j a b c x y := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  rcases h with h | ⟨t, o, u, sd, ha, rfl, he, rfl, one⟩
  · have h' := h
    unfold R6 at h'
    have keep : ¬ Capture a b c 6 e f := by unfold Capture Near; omega
    refine ⟨keep, key_reply D (by omega) keep (Or.inr h), ?_⟩
    intro x y st
    have k7 := st.k7
    have k5 := st.k6
    refine Or.inl ⟨?_, Or.inr (by unfold Near; omega)⟩
    unfold Free
    omega
  · obtain ⟨v, sw⟩ := Sd.swap hc sd
    have sd' := sd
    unfold Sd at sd'
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
    exact Or.inr (Or.inr (Or.inl ⟨⟨x, t, v, sw, rfl, rfl, Or.inl (by unfold Within1; omega)⟩, one⟩))

set_option maxHeartbeats 4000000 in
/-- Outside the top guard the pawn on the seventh wins. -/
theorem sev_cover {a b c e f : Nat} (D : DomS a b c 6 e f) (hc : 2 ≤ c) (n : ¬ TS a b c 6 e f) :
    SevS 2 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k3 := D.1.k3
  have k4 := D.k4
  by_cases pr : Prom a b c e f
  · exact Or.inl pr
  have pr' := pr
  unfold Prom Free at pr'
  by_cases top : a = c ∧ b = 7
  · exact Or.inr (Or.inl ⟨top.1, top.2, by omega⟩)
  have ntop : ¬ (a = c ∧ b = 7) := top
  by_cases block : e = c ∧ f = 7
  · obtain ⟨rfl, rfl⟩ := block
    refine Or.inr (Or.inr (Or.inr ⟨⟨rfl, rfl, ?_⟩, by omega⟩))
    apply Classical.byContradiction
    intro q
    exact n ⟨by omega, rfl, Or.inl ⟨rfl, rfl, fun g => q (Or.inl g), fun g => q (Or.inr g.2)⟩⟩
  have w : Near e f c 7 := by
    by_cases g : Near e f c 7
    · exact g
    · exfalso; apply pr; exact ⟨by unfold Free; omega, Or.inl g⟩
  unfold Near at w
  have row : f = 6 := by omega
  subst row
  by_cases g : e + 1 = c
  · refine Or.inr (Or.inr (Or.inl ⟨⟨c - 1, c + 1, c - 2, Or.inr ⟨by omega, rfl, by omega⟩, by omega, rfl, ?_⟩, by omega⟩))
    apply Classical.byContradiction
    intro q
    exact n ⟨by omega, rfl, Or.inr (Or.inl ⟨g, rfl, fun z => q (Or.inl z), fun z => q (Or.inr z)⟩)⟩
  · have g2 : e = c + 1 := by omega
    refine Or.inr (Or.inr (Or.inl ⟨⟨c + 1, c - 1, c + 2, Or.inl ⟨rfl, by omega, rfl⟩, g2, rfl, ?_⟩, by omega⟩))
    apply Classical.byContradiction
    intro q
    exact n ⟨by omega, rfl, Or.inr (Or.inr ⟨g2, rfl, fun z => q (Or.inl z), fun z => q (Or.inr z)⟩)⟩

/-- The winning plan with a bishop or centre pawn on the seventh rank. -/
def sevPlan : Plan where
  S j a b c d e f := 2 ≤ c ∧ j ≤ 2 ∧ d = 6 ∧ SevS j a b c e f
  W j a b c d e f := 2 ≤ c ∧ j ≤ 2 ∧ d = 6 ∧ SevW j a b c e f
  S_le := fun h => by have := h.2.1; omega
  W_le := fun h => by have := h.2.1; omega
  strong := by
    intro j a b c d e f D h
    obtain ⟨hc, hj, rfl, h⟩ := h
    rcases sev_strong D hc hj h with q | ⟨i, rfl, x, y, st, w⟩
    · exact Or.inl q
    · exact Or.inr ⟨i, rfl, x, y, st, hc, by omega, rfl, w⟩
  weak := by
    intro j a b c d e f D h
    obtain ⟨hc, hj, rfl, h⟩ := h
    obtain ⟨q1, q2, q3⟩ := sev_weak D hc h
    exact ⟨q1, q2, fun x y st => ⟨j, Nat.le_refl j, hc, hj, rfl, q3 x y st⟩⟩

/-- A bishop or centre pawn on the seventh rank, pawn owner to move, outside the top
guard: an actual win. With `fresh_top_hold` this classifies these roots. -/
theorem fresh_seventh_win {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 2 ≤ mx ps ps) (top : height σ ps = 6)
    (out : ¬ TS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  rw [top] at D out
  have cov := sev_cover D file out
  exact fresh_plan_strong (P := sevPlan) (j := 2) h fresh turn safe ⟨file, by omega, top, cov⟩

end EndgameChess.Rules.KPK.Coord
