import EndgameChess.Rules.KPK.Coord.FourWin

/-! Fourth rank, the winning side: the king races to a key square. The key squares of a
pawn on `(c,3)` are the three squares `(p,5)` two ranks ahead. If the king is nearer to
one of them than the lone king, and the pawn cannot be taken on the way (the lone king is
farther from it than the king from the key square, or the king guards it), the king walks
there and the pawn then advances. Each step keeps the race with the same key square. -/
namespace EndgameChess.Rules.KPK.Coord

/-- The king is within `m` steps of the key square `(p,5)`, the lone king is not, and the
pawn cannot fall first. -/
def Key3 (m a b c e f p : Nat) : Prop :=
  (p = c + 1 ∨ p = c ∨ p + 1 = c) ∧ Ch a b p 5 m ∧ ¬ Ch e f p 5 m ∧
    (¬ Ch e f c 3 m ∨ Near a b c 3)

/-- The king beside the square in front of the pawn, the lone king no higher. -/
def Bes3 (a b c f : Nat) : Prop := b = 4 ∧ (a = c + 1 ∨ a + 1 = c) ∧ f ≤ 4

/-- A king that guards the square in front of the pawn, with the lone king below the
sixth rank, lets the pawn advance: the lone king cannot take it and never reaches the
fifth-rank guard, which needs it on the seventh rank or the king off the guarding squares. -/
theorem bes_push {a b c e f : Nat} (D : DomS a b c 3 e f) (h : Bes3 a b c f) :
    PushOK3 a b c e f := by
  obtain ⟨hb, ha, hf⟩ := h
  have k1 := D.1.k1
  refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
  · unfold Capture Near
    omega
  · intro X Y st s
    obtain ⟨⟨m1, m2, m3, m4⟩, m5, m6⟩ := WeakStep.bounds st
    obtain ⟨nk, -, h4 | h4⟩ := s
    · omega
    · exact h4.1 (by unfold B4; omega)

/-- On a key square the pawn advances at once. -/
theorem key0_push {a b c e f p : Nat} (D : DomS a b c 3 e f) (h : Key3 0 a b c e f p) :
    PushOK3 a b c e f := by
  obtain ⟨hp, hk, -, -⟩ := h
  have k1 := D.1.k1
  unfold Ch at hk
  refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
  · unfold Capture Near
    omega
  · intro X Y _ s
    exact s.1 (by unfold K4; omega)

theorem key_mono {m n a b c e f p : Nat} (le : n ≤ m) (hk : Ch a b p 5 n) (h : Key3 m a b c e f p) :
    Key3 n a b c e f p := by
  obtain ⟨hp, -, hl, hs⟩ := h
  refine ⟨hp, hk, fun g => hl (by unfold Ch at *; omega), ?_⟩
  rcases hs with hs | hs
  · exact Or.inl (fun g => hs (by unfold Ch at *; omega))
  · exact Or.inr hs

/-- A race is either at the key square or at an exact distance. -/
theorem key_exact {m a b c e f p : Nat} (h : Key3 m a b c e f p) :
    Key3 0 a b c e f p ∨ ∃ n, n + 1 ≤ m ∧ Key3 (n + 1) a b c e f p ∧ ¬ Ch a b p 5 n := by
  induction m with
  | zero => exact Or.inl h
  | succ m ih =>
    by_cases g : Ch a b p 5 m
    · rcases ih (key_mono (Nat.le_succ m) g h) with q | ⟨n, hn, q, ex⟩
      · exact Or.inl q
      · exact Or.inr ⟨n, by omega, q, ex⟩
    · exact Or.inr ⟨m, Nat.le_refl _, h, g⟩

/-- A guarding king leaves the pawn only from the rank in front of it, onto the key rank. -/
theorem tw_leave {a b c p x y : Nat} (hp : p = c + 1 ∨ p = c ∨ p + 1 = c)
    (tw : Toward a b p 5 x y) (hs : Near a b c 3) (g : ¬ Near x y c 3) (np : ¬ (x = c ∧ y = 3)) :
    b = 4 ∧ y = 5 ∧ x ≤ c + 1 ∧ c ≤ x + 1 := by
  unfold Toward at tw
  unfold Near at hs g
  omega

/-- From the rank in front, the race to the key square is one or two steps. -/
theorem leave_m {a c p m : Nat} (hp : p = c + 1 ∨ p = c ∨ p + 1 = c) (ha : a ≤ c + 1 ∧ c ≤ a + 1)
    (hk : Ch a 4 p 5 (m + 1)) (ex : ¬ Ch a 4 p 5 m) :
    m = 0 ∨ (m = 1 ∧ ((a + 1 = c ∧ p = c + 1) ∨ (a = c + 1 ∧ p + 1 = c))) := by
  unfold Ch at hk ex
  omega

/-- After the king leaves the pawn two steps from the key square, the lone king cannot
come next to the pawn. -/
theorem leave_far {c p e f X Y : Nat} (hp : p = c + 1 ∨ p + 1 = c)
    (hl : ¬ Ch e f p 5 2) (hf : 5 ≤ f) (st : Near e f X Y)
    (k8 : ¬ (Y = 4 ∧ (X = c + 1 ∨ X + 1 = c))) : ¬ Ch X Y c 3 1 := by
  unfold Ch at *
  unfold Near at st
  omega

set_option maxHeartbeats 4000000 in
/-- The step towards the key square keeps the race. -/
theorem key_tw {m a b c e f p x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : Key3 (m + 1) a b c e f p) (ex : ¬ Ch a b p 5 m) (tw : Toward a b p 5 x y)
    (np : ¬ (x = c ∧ y = 3)) (nc : ¬ Capture x y c 3 e f) (nb : ¬ Bes3 a b c f) :
    KingStep a b c 3 e f x y ∧ ∀ X Y, WeakStep x y c 3 e f X Y → Key3 m x y c X Y p := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, hk, hl, hs⟩ := h
  have ks : KingStep a b c 3 e f x y := by
    unfold Ch at hk hl ex
    unfold Toward at tw
    exact ⟨by unfold Near; omega, by omega, by omega, np, by unfold Apart; omega⟩
  refine ⟨ks, fun X Y st => ⟨hp, ?_, ?_, ?_⟩⟩
  · unfold Ch at hk ex ⊢
    unfold Toward at tw
    omega
  · have n := st.1
    unfold Ch at hl ⊢
    unfold Near at n
    omega
  rcases hs with hs | hs
  · left
    have n := st.1
    unfold Ch at hs ⊢
    unfold Near at n
    omega
  by_cases g : Near x y c 3
  · exact Or.inr g
  left
  obtain ⟨rfl, rfl, x1, x2⟩ := tw_leave hp tw hs g np
  have ha : a ≤ c + 1 ∧ c ≤ a + 1 := by
    unfold Near at hs
    omega
  rcases leave_m hp ha hk ex with rfl | ⟨rfl, side⟩
  · have k6 := st.k6
    unfold Ch
    omega
  · have hf : 5 ≤ f := by
      unfold Bes3 at nb
      omega
    have k1 := D.1.k1
    exact leave_far (by omega) hl hf st.1 st.k8

set_option maxHeartbeats 4000000 in
/-- When the step towards the key square would land on the pawn, the king steps beside the
pawn instead, which keeps the race and guards the pawn. -/
theorem key_round {m a b c e f p x : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : Key3 (m + 1) a b c e f p) (tw : Toward a b p 5 c 3)
    (hx : (¬ a = c ∧ x = a) ∨ (a = c ∧ x = c + 1)) :
    KingStep a b c 3 e f x 3 ∧ ¬ Capture x 3 c 3 e f ∧
      ∀ X Y, WeakStep x 3 c 3 e f X Y → Key3 m x 3 c X Y p := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, hk, hl, -⟩ := h
  have pos : b = 2 ∧ a ≤ c + 1 ∧ c ≤ a + 1 ∧ (a = c → p = c) := by
    unfold Toward at tw
    omega
  obtain ⟨rfl, a1, a2, a3⟩ := pos
  have g : Near x 3 c 3 := by
    unfold Near
    omega
  refine ⟨⟨by unfold Near; omega, by omega, by omega, by omega, ?_⟩, ?_, ?_⟩
  · unfold Ch at hk hl
    unfold Apart
    omega
  · unfold Capture
    exact fun q => q.2 g
  · intro X Y st
    have n := st.1
    refine ⟨hp, ?_, ?_, Or.inr g⟩
    · unfold Ch at hk ⊢
      omega
    · unfold Ch at hk hl ⊢
      unfold Near at n
      omega

set_option maxHeartbeats 4000000 in
/-- When the step towards the key square would let the lone king take the pawn, the king
stands in front of the pawn, and it steps beside it; the pawn then advances. -/
theorem key_def {m a b c e f p x y z : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : Key3 (m + 1) a b c e f p) (tw : Toward a b p 5 x y) (np : ¬ (x = c ∧ y = 3))
    (cap : Capture x y c 3 e f) (nb : ¬ Bes3 a b c f)
    (hz : (c ≤ p ∧ z = c + 1) ∨ (p + 1 = c ∧ z + 1 = c)) :
    KingStep a b c 3 e f z 4 ∧ ¬ Capture z 4 c 3 e f ∧
      ∀ X Y, WeakStep z 4 c 3 e f X Y → Bes3 z 4 c Y := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, hk, hl, hs⟩ := h
  obtain ⟨cn, cg⟩ := cap
  have hs' : Near a b c 3 := by
    rcases hs with hs | hs
    · exfalso
      unfold Ch at hs
      unfold Near at cn
      omega
    · exact hs
  obtain ⟨rfl, rfl, -, -⟩ := tw_leave hp tw hs' cg np
  have k1 := D.1.k1
  have hk2 := D.1.k2
  have ha : a = c := by
    unfold Bes3 at nb
    unfold Near at hs' cn
    omega
  subst ha
  have hf : f ≤ 2 := by
    unfold Near at cn
    unfold Apart at k1
    omega
  have g : Near z 4 a 3 := by
    unfold Near
    omega
  refine ⟨⟨by unfold Near; omega, by omega, by omega, by omega, by unfold Apart; omega⟩,
    fun q => q.2 g, fun X Y st => ?_⟩
  have n := st.1
  unfold Near at n
  exact ⟨rfl, by omega, by omega⟩

/-- The king's move in a race. -/
theorem key_move {m a b c e f p : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : Key3 (m + 1) a b c e f p) (ex : ¬ Ch a b p 5 m) (nb : ¬ Bes3 a b c f) :
    ∃ x y, KingStep a b c 3 e f x y ∧ ¬ Capture x y c 3 e f ∧
      ∀ X Y, WeakStep x y c 3 e f X Y → Key3 m x y c X Y p ∨ Bes3 x y c Y := by
  obtain ⟨x, y, tw⟩ := toward_ex a b p 5
  by_cases np : x = c ∧ y = 3
  · obtain ⟨h1, h2⟩ := np
    rw [h1, h2] at tw
    have hx : ∃ z, (¬ a = c ∧ z = a) ∨ (a = c ∧ z = c + 1) := by
      by_cases g : a = c
      · exact ⟨c + 1, Or.inr ⟨g, rfl⟩⟩
      · exact ⟨a, Or.inl ⟨g, rfl⟩⟩
    obtain ⟨z, hz⟩ := hx
    obtain ⟨st, nc, all⟩ := key_round D hc h tw hz
    exact ⟨z, 3, st, nc, fun X Y w => Or.inl (all X Y w)⟩
  by_cases cap : Capture x y c 3 e f
  · have hp := h.1
    have hz : ∃ z, (c ≤ p ∧ z = c + 1) ∨ (p + 1 = c ∧ z + 1 = c) := by
      by_cases g : c ≤ p
      · exact ⟨c + 1, Or.inl ⟨g, rfl⟩⟩
      · exact ⟨c - 1, Or.inr ⟨by omega, by omega⟩⟩
    obtain ⟨z, hz⟩ := hz
    obtain ⟨st, nc, all⟩ := key_def D hc h tw np cap nb hz
    exact ⟨z, 4, st, nc, fun X Y w => Or.inr (all X Y w)⟩
  · obtain ⟨st, all⟩ := key_tw D hc h ex tw np cap nb
    exact ⟨x, y, st, cap, fun X Y w => Or.inl (all X Y w)⟩

theorem dom_push3 {a b c e f : Nat} (D : DomS a b c 3 e f) (fr : Free a b e f c 4) :
    Dom a b c 4 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨u1, u2, u3, by omega, by omega, u6, u7, fr.1, fr.2, D.1.k1⟩

theorem dom_step3 {a b c e f x y : Nat} (D : DomS a b c 3 e f) (st : KingStep a b c 3 e f x y) :
    Dom x y c 3 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨st.2.1, st.2.2.1, u3, by omega, by omega, u6, u7, st.k6, D.1.k3, st.2.2.2.2⟩

/-- Fourth-rank positions in the race class with phase at most `j`. -/
def K3 (j a b c e f : Nat) : Prop :=
  PushOK3 a b c e f ∨ Bes3 a b c f ∨ ∃ p m, m ≤ j ∧ Key3 m a b c e f p

/-- The lone king to move after a race step: no capture, a reply, and every reply in the
race class with phase at most `i`. -/
def K3win (i x y c e f : Nat) : Prop :=
  ¬ Capture x y c 3 e f ∧ (∃ X Y, WeakStep x y c 3 e f X Y) ∧
    ∀ X Y, WeakStep x y c 3 e f X Y → K3 i x y c X Y

/-- A race position: push, or a race step spending one phase. -/
theorem k3_move {j a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : K3 j a b c e f) :
    PushOK3 a b c e f ∨ ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 3 e f x y ∧ K3win i x y c e f := by
  rcases h with h | h | ⟨p, m, hm, k⟩
  · exact Or.inl h
  · exact Or.inl (bes_push D h)
  rcases key_exact k with k0 | ⟨n, hn, k, ex⟩
  · exact Or.inl (key0_push D k0)
  by_cases nb : Bes3 a b c f
  · exact Or.inl (bes_push D nb)
  obtain ⟨x, y, st, nc, all⟩ := key_move D hc k ex nb
  refine Or.inr ⟨j - 1, by omega, x, y, st, nc,
    weak_reply (dom_step3 D st) (Or.inr (Or.inl (by omega))) nc, fun X Y w => ?_⟩
  rcases all X Y w with q | q
  · exact Or.inr (Or.inr ⟨p, n, by omega, q⟩)
  · exact Or.inr (Or.inl q)

/-- A race lasts at most six steps. -/
theorem key_le {m a b c e f p : Nat} (D : DomS a b c 3 e f) (h : Key3 m a b c e f p) : m ≤ 6 := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, -, hl, -⟩ := h
  unfold Ch at hl
  omega

/-- The race class on top of the fifth-rank plan. -/
def fourKeyPlan : Plan where
  S j a b c d e f := knFivePlan.S j a b c d e f ∨ (d = 3 ∧ 1 ≤ c ∧ j ≤ 20 ∧ K3 j a b c e f)
  W j a b c d e f := knFivePlan.W j a b c d e f ∨ (d = 3 ∧ 1 ≤ c ∧ j ≤ 20 ∧ K3win j a b c e f)
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
    · rcases k3_move D hc k with ⟨fr, lost⟩ | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (Or.inl ⟨fr, by omega, 13, by omega,
          Or.inl (Or.inr ⟨rfl, hc, Nat.le_refl 13, lost4_w4win (dom_push3 D fr) hc lost⟩)⟩)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inr ⟨rfl, hc, by omega, w⟩⟩
  weak := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, keep, reply, all⟩
    · obtain ⟨q1, q2, q3⟩ := knFivePlan.weak D h
      refine ⟨q1, q2, fun x y st => ?_⟩
      obtain ⟨i, le, s⟩ := q3 x y st
      exact ⟨i, le, Or.inl s⟩
    · exact ⟨keep, reply, fun x y st => ⟨j, Nat.le_refl j, Or.inr ⟨rfl, hc, hj, all x y st⟩⟩⟩

open EndgameChess.KK in
/-- Fourth rank, pawn owner to move: if the king is nearer than the lone king to a square
two ranks ahead of the pawn on its file or the next one, and the lone king is farther from
the pawn than that or the king guards the pawn, the pawn owner wins. -/
theorem fresh_four_key_win {σ : Colour} {q : Position} {sk ps wk : Square} {p m : Nat}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (k : Key3 m (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk) p) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  rw [rank] at D
  have hm := key_le D k
  exact fresh_plan_strong (P := fourKeyPlan) (j := m) h fresh turn safe
    (Or.inr ⟨rank, file, by omega, Or.inr (Or.inr ⟨p, m, Nat.le_refl m, k⟩)⟩)

end EndgameChess.Rules.KPK.Coord
