import EndgameChess.Rules.KPK.Coord.Five4
import EndgameChess.Rules.KPK.Coord.SixPlan

/-! Wins with a bishop or centre pawn on the fifth rank, outside the guard: definitions and
the short classes. The pawn advances when every reply then leaves the sixth-rank guard; a
king on a key square needs at most two steps before that; a king beside the pawn steps to
a key square. -/
namespace EndgameChess.Rules.KPK.Coord

/-- The king wins the race to `(p,q)` in `n` moves. -/
def Won (a b c e f p q n : Nat) : Prop := KR a b c p q n ∧ ¬ WR e f c p q n

/-- One of the four key squares beside the pawn's file. -/
def KeyT (c p q : Nat) : Prop := (p = c + 1 ∨ p + 1 = c) ∧ (q = 5 ∨ q = 6)

/-- The pawn advances and every reply leaves the sixth-rank guard. -/
def PushOK (a b c e f : Nat) : Prop := Free a b e f c 5 ∧ W5win 10 a b c e f

/-- The few positions with no race won that need a king step first. -/
def RestM (j a b c e f : Nat) : Prop :=
  ∃ u w, Sw c u w ∧
    ((1 ≤ j ∧ a = w ∧ b = 3 ∧ e = w ∧ f = 6) ∨ (1 ≤ j ∧ a = w ∧ b = 7 ∧ e = w ∧ f = 4) ∨
     (6 ≤ j ∧ a = w ∧ (b = 4 ∨ b = 5) ∧ e = u ∧ f = 7) ∨
     (7 ≤ j ∧ u = c + 2 ∧ a = w + 1 ∧ (b = 4 ∨ b = 5) ∧ e = w ∧ f = 7))

/-- Phase of a fifth-rank position with the pawn owner to move. -/
def Ph4 (j a b c e f : Nat) : Prop :=
  PushOK a b c e f ∨ (1 ≤ j ∧ a = c ∧ b = 5) ∨ (2 ≤ j ∧ K4 a b c) ∨ (3 ≤ j ∧ B4 a b c) ∨
    (∃ p q n, KeyT c p q ∧ 1 ≤ n ∧ n + 4 ≤ j ∧ Won a b c e f p q n) ∨ RestM j a b c e f

/-- Lone king to move on the fifth rank: no capture, a reply, and every reply is outside
the guard with phase at most `i`. -/
def W4win (i x y c e f : Nat) : Prop :=
  ¬ Capture x y c 4 e f ∧ (∃ X Y, WeakStep x y c 4 e f X Y) ∧
    ∀ X Y, WeakStep x y c 4 e f X Y → ¬ S4 x y c X Y ∧ Ph4 i x y c X Y

/-- A move of the pawn owner on the fifth rank that spends one phase. -/
def Mv4 (j a b c e f : Nat) : Prop :=
  PushOK a b c e f ∨ ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 4 e f x y ∧ W4win i x y c e f

theorem ph4_mono {i j a b c e f : Nat} (le : i ≤ j) (h : Ph4 i a b c e f) : Ph4 j a b c e f := by
  rcases h with h | h | h | h | ⟨p, q, n, kt, n1, nj, w⟩ | ⟨u, w, sw, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, n, kt, n1, by omega, w⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, w, sw, ?_⟩))))
    rcases h with h | h | h | h
    · exact Or.inl ⟨by omega, h.2⟩
    · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))

theorem w4win_mono {i j x y c e f : Nat} (le : i ≤ j) (h : W4win i x y c e f) :
    W4win j x y c e f :=
  ⟨h.1, h.2.1, fun X Y st => ⟨(h.2.2 X Y st).1, ph4_mono le (h.2.2 X Y st).2⟩⟩

theorem dom_push4 {a b c e f : Nat} (D : DomS a b c 4 e f) (fr : Free a b e f c 5) :
    Dom a b c 5 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨u1, u2, u3, by omega, by omega, u6, u7, fr.1, fr.2, D.1.k1⟩

theorem dom_step4 {a b c e f x y : Nat} (D : DomS a b c 4 e f) (st : KingStep a b c 4 e f x y) :
    Dom x y c 4 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨st.2.1, st.2.2.1, u3, by omega, by omega, u6, u7, st.k6, D.1.k3, st.2.2.2.2⟩

theorem domS_reply {x y c d e f X Y : Nat} (D : Dom x y c d e f) (st : WeakStep x y c d e f X Y) :
    DomS x y c d X Y := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨⟨u1, u2, u3, u4, u5, st.2.1, st.2.2.1, D.k2, st.k6, st.k7⟩, st.k8⟩

/-- A push is good once the pawn is safe and no reply reaches the sixth-rank guard. -/
theorem pushOK_of {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (fr : Free a b e f c 5)
    (keep : ¬ Capture a b c 5 e f) (no : ¬ (c = 2 ∧ e = 0 ∧ f = 7 ∧ a = 1 ∧ b = 5))
    (all : ∀ x y, WeakStep a b c 5 e f x y → ¬ S5 a b c x y) : PushOK a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  refine ⟨fr, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))), keep,
    six_reply (dom_push4 D fr) hc keep no, all⟩
  unfold Ch
  omega

set_option maxHeartbeats 4000000 in
/-- Outside the pawn's square the pawn advances. -/
theorem push_out {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (nk : ¬ (a = c ∧ b = 5))
    (out : ¬ Sq4 c e f) : PushOK a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Sq4 at out
  refine pushOK_of D hc ⟨nk, by omega⟩ (by unfold Capture Near; omega) (by omega) ?_
  intro x y st h
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  obtain ⟨-, b1, b2, b3, -⟩ := h
  omega

set_option maxHeartbeats 4000000 in
/-- A king on a seventh-rank key square: the pawn advances. -/
theorem push_key6 {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (k : K4 a b c)
    (hb : b = 6) : PushOK a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  unfold K4 at k
  refine pushOK_of D hc ⟨by omega, by omega⟩ (by unfold Capture Near; omega) (by omega) ?_
  intro x y _
  exact nd_key (by unfold Key5; omega)

set_option maxHeartbeats 4000000 in
/-- A king on a sixth-rank key square beside the pawn's file: the pawn advances unless the
lone king can oppose on the last rank. -/
theorem push_key5 {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (ha : a = c + 1 ∨ a + 1 = c) (hb : b = 5) (n1 : ¬ (e = c ∧ f = 7))
    (n2 : ¬ (f = 7 ∧ ((a = c + 1 ∧ e = c + 2) ∨ (a + 1 = c ∧ e + 2 = c)))) :
    PushOK a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  refine pushOK_of D hc ⟨by omega, by omega⟩ (by unfold Capture Near; omega) (by omega) ?_
  intro x y st
  obtain ⟨⟨m1, m2, m3, m4⟩, m5, m6⟩ := WeakStep.bounds st
  have k5 := st.k5
  exact nd_beside (by unfold Beside; omega) (by omega)

/-- With the king on a key square the lone king's replies are again key-square positions. -/
theorem w4win_key {i x y c e f : Nat} (D : Dom x y c 4 e f) (k : K4 x y c) (hi : 2 ≤ i)
    (keep : ¬ Capture x y c 4 e f) : W4win i x y c e f :=
  ⟨keep, weak_reply D (Or.inr (Or.inl (Nat.le_refl 4))) keep,
    fun _ _ _ => ⟨fun h => h.1 k, Or.inr (Or.inr (Or.inl ⟨hi, k⟩))⟩⟩

set_option maxHeartbeats 4000000 in
/-- The king directly ahead of the pawn steps aside, and then the pawn advances. -/
theorem mv_front {j a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (hj : 1 ≤ j)
    (ha : a = c) (hb : b = 5) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  subst ha hb
  obtain ⟨x, y, hx, hy⟩ : ∃ x y, (x = a + 1 ∨ x + 1 = a) ∧
      ((y = 6 ∧ f = 7 ∧ (x = a + 1 ∧ e + 1 = a ∨ x + 1 = a ∧ e = a + 1)) ∨
       (y = 5 ∧ ¬ (f = 7 ∧ (e = a + 1 ∨ e + 1 = a)) ∧ (x = a + 1 ∧ e ≤ a ∨ x + 1 = a ∧ a < e))) := by
    by_cases g1 : f = 7 ∧ e + 1 = a
    · exact ⟨a + 1, 6, by omega, by omega⟩
    by_cases g2 : f = 7 ∧ e = a + 1
    · exact ⟨a - 1, 6, by omega, by omega⟩
    by_cases g3 : e ≤ a
    · exact ⟨a + 1, 5, by omega, by omega⟩
    · exact ⟨a - 1, 5, by omega, by omega⟩
  have st : KingStep a 5 a 4 e f x y := by
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture x y a 4 e f := by
    unfold Capture Near
    omega
  refine Or.inr ⟨j - 1, by omega, x, y, st, w4win_mono (Nat.zero_le _) ⟨keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩⟩
  have kx : K4 x y a := by unfold K4; omega
  refine ⟨fun h => h.1 kx, Or.inl ?_⟩
  have D2 := domS_reply D' ws
  obtain ⟨⟨m1, m2, m3, m4⟩, m5, m6⟩ := WeakStep.bounds ws
  have k5 := ws.k5
  have k7 := ws.k7
  rcases hy with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
  · exact push_key6 D2 hc kx rfl
  · exact push_key5 D2 hc hx rfl (by omega) (by omega)

set_option maxHeartbeats 4000000 in
/-- A king on a key square wins within two king steps. -/
theorem mv_key {j a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (hj : 2 ≤ j)
    (k : K4 a b c) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k' := k
  unfold K4 at k'
  by_cases b6 : b = 6
  · exact Or.inl (push_key6 D hc k b6)
  have hb : b = 5 := by omega
  by_cases mid : a = c
  · exact mv_front D hc (by omega) mid hb
  have ha : a = c + 1 ∨ a + 1 = c := by omega
  subst hb
  by_cases g1 : e = c ∧ f = 7
  · have st : KingStep a 5 c 4 e f c 5 := by
      unfold KingStep Near Apart
      omega
    have D' := dom_step4 D st
    have keep : ¬ Capture c 5 c 4 e f := by
      unfold Capture Near
      omega
    refine Or.inr ⟨j - 1, by omega, c, 5, st, keep,
      weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y _ => ?_⟩
    exact ⟨fun h => h.1 (by unfold K4; omega), Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)⟩
  by_cases g2 : f = 7 ∧ ((a = c + 1 ∧ e = c + 2) ∨ (a + 1 = c ∧ e + 2 = c))
  · have st : KingStep a 5 c 4 e f c 6 := by
      unfold KingStep Near Apart
      omega
    have D' := dom_step4 D st
    have keep : ¬ Capture c 6 c 4 e f := by
      unfold Capture Near
      omega
    have kx : K4 c 6 c := by unfold K4; omega
    refine Or.inr ⟨j - 1, by omega, c, 6, st, w4win_mono (Nat.zero_le _) ⟨keep,
      weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩⟩
    exact ⟨fun h => h.1 kx, Or.inl (push_key6 (domS_reply D' ws) hc kx rfl)⟩
  · exact Or.inl (push_key5 D hc ha rfl g1 g2)

set_option maxHeartbeats 4000000 in
/-- A king beside the pawn outside the guard steps to a key square. -/
theorem mv_beside4 {j a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (hj : 3 ≤ j)
    (bes : B4 a b c) (out : ¬ S4 a b c e f) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  have bes' := bes
  unfold B4 at bes'
  obtain ⟨rfl, side⟩ := bes'
  obtain ⟨x, hx, ap⟩ : ∃ x, (x = a ∨ x = c) ∧ Apart x 5 e f := by
    by_cases g : Apart a 5 e f
    · exact ⟨a, Or.inl rfl, g⟩
    by_cases g2 : Apart c 5 e f
    · exact ⟨c, Or.inr rfl, g2⟩
    exfalso
    apply out
    unfold Apart at g g2
    refine ⟨by unfold K4; omega, by unfold Sq4; omega, Or.inl ⟨bes, by omega, by omega⟩⟩
  have st : KingStep a 4 c 4 e f x 5 := by
    refine ⟨?_, by omega, by omega, by omega, ap⟩
    unfold Near
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture x 5 c 4 e f := by
    unfold Capture Near
    omega
  exact Or.inr ⟨j - 1, by omega, x, 5, st,
    w4win_key D' (by unfold K4; omega) (by omega) keep⟩

end EndgameChess.Rules.KPK.Coord
