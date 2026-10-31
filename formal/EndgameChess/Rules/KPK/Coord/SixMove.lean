import EndgameChess.Rules.KPK.Coord.SixWin

/-! The strong moves on the sixth rank, one class at a time. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- A planned strong move with the pawn on the sixth rank. -/
def Mv (j a b c e f : Nat) : Prop :=
  (Free a b e f c 6 ∧ W6 a b c e f) ∨
    ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 5 e f x y ∧ W5win i x y c e f

theorem dom_step {a b c e f x y : Nat} (D : DomS a b c 5 e f) (st : KingStep a b c 5 e f x y) :
    Dom x y c 5 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨st.2.1, st.2.2.1, u3, u4, u5, u6, u7, st.k6, D.1.k3, st.2.2.2.2⟩

theorem dom_push {a b c e f : Nat} (D : DomS a b c 5 e f) (fr : Free a b e f c 6) :
    Dom a b c 6 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨u1, u2, u3, by omega, by omega, u6, u7, fr.1, fr.2, D.1.2.2.2.2.2.2.2.2.2⟩

theorem w_key {j a b c e f t o u : Nat} (D : Dom a b c 5 e f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (ha : a = t) (hb : b = 6 ∨ b = 7) (keep : ¬ Capture a b c 5 e f) : W5win j a b c e f := by
  unfold Sd at sd
  have nk : Key5 a b c := by unfold Key5; omega
  refine ⟨Or.inl ⟨by omega, by omega⟩, keep, key_reply D (by omega) keep
    (Or.inl ⟨by unfold Cl; omega, by omega, by omega, by unfold Stale; omega⟩), ?_⟩
  exact fun x y _ => nd_key nk

theorem w_c6 {j a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 2 ≤ c) (hj : 1 ≤ j)
    (ha : a = c) (hb : b = 6) : W5win j a b c e f := by
  have nk : Key5 a b c := by unfold Key5; omega
  have keep : ¬ Capture a b c 5 e f := by unfold Capture Near; omega
  refine ⟨Or.inr (Or.inl ⟨hj, Or.inl ⟨ha, by omega⟩⟩), keep, key_reply D (by omega) keep
    (Or.inl ⟨by unfold Cl; omega, by omega, by omega, by unfold Stale; omega⟩), ?_⟩
  exact fun x y _ => nd_key nk

theorem w_bes {j a b c e f t o u : Nat} (D : Dom a b c 5 e f) (hc : 2 ≤ c) (hj : 2 ≤ j) (sd : Sd c t o u)
    (ha : a = t) (hb : b = 5) (opp : (e = t ∧ f = 7) ∨ ¬ Near e f t 7)
    (ns : ¬ (c = 2 ∧ t = 1 ∧ e = 0 ∧ f = 7)) : W5win j a b c e f := by
  unfold Sd at sd
  have bs : Beside a b c := by unfold Beside; omega
  have keep : ¬ Capture a b c 5 e f := by unfold Capture Near; omega
  refine ⟨Or.inr (Or.inr (Or.inl ⟨hj, bs⟩)), keep, six_reply D hc keep (by omega), ?_⟩
  intro x y st
  apply nd_beside bs
  have k5 := st.k5
  obtain ⟨n, -, -⟩ := st
  unfold Near at n opp
  omega

theorem w_close {j a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 2 ≤ c) (ph : Phi j a b c)
    (a1 : ¬ Arr 1 a b c) (p2 : Ch a b c 5 2) (nb : ¬ Beside a b c) (y7 : b ≠ 7) (b1 : ¬ Bl 1 c e f)
    (keep : ¬ Capture a b c 5 e f) (ns : ¬ (c = 2 ∧ e = 0 ∧ f = 7 ∧ a = 1 ∧ b = 5)) :
    W5win j a b c e f := by
  refine ⟨ph, keep, six_reply D hc keep ns, ?_⟩
  intro x y st
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  apply nd_close hc a1 p2 nb (Or.inl y7)
  unfold Bl Ch at b1 ⊢
  omega

set_option maxHeartbeats 4000000 in
/-- The pawn reaches the seventh with the lone king forced off the promotion square. -/
theorem w6_evict {a b c e f t o u : Nat} (D : Dom a b c 6 e f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (ha : a = t) (hb : b = 5) (he : e = c) (hf : f = 7) : W6 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Sd at sd
  have keep : ¬ Capture a b c 6 e f := by unfold Capture Near; omega
  refine ⟨keep, ⟨o, 6, by unfold WeakStep Near Apart Att; omega⟩, ?_⟩
  intro x y st h
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  have k5 := st.k5
  have k6 := st.k6
  have k7 := st.k7
  have k8 := st.k8
  obtain ⟨-, -, q | q | q⟩ := h
  · unfold Block7 at q; omega
  · unfold SideL Within1 at q; omega
  · unfold SideR Within1 at q; omega

theorem two_sides {c a : Nat} (hc : 2 ≤ c) (h : a = c + 1 ∨ a + 1 = c) : ∃ o u, Sd c a o u := by
  rcases h with h | h
  · exact ⟨c - 1, c + 2, Or.inl ⟨h, by omega, rfl⟩⟩
  · exact ⟨c + 1, c - 2, Or.inr ⟨h, rfl, by omega⟩⟩

set_option maxHeartbeats 4000000 in
/-- The king is ahead of the pawn. -/
theorem mv_ahead {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (ph : Phi j a b c)
    (ha : a = c + 1 ∨ a + 1 = c ∨ a = c) (hb : 6 ≤ b) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  by_cases mid : a = c
  · unfold Phi Ch Beside at ph
    have hj : 1 ≤ j := by omega
    refine Or.inr ⟨j - 1, by omega, ?_⟩
    by_cases g : Apart (c + 1) 6 e f
    · obtain ⟨o, u, sd⟩ := two_sides (a := c + 1) hc (Or.inl rfl)
      have st : KingStep a b c 5 e f (c + 1) 6 := by unfold Apart at g; unfold KingStep Near Apart; omega
      refine ⟨c + 1, 6, st, w_key (dom_step D st) hc sd rfl (Or.inl rfl) ?_⟩
      unfold Capture Near; omega
    · obtain ⟨o, u, sd⟩ := two_sides (a := c - 1) hc (Or.inr (by omega))
      unfold Apart at g
      have st : KingStep a b c 5 e f (c - 1) 6 := by unfold KingStep Near Apart; omega
      refine ⟨c - 1, 6, st, w_key (dom_step D st) hc sd rfl (Or.inl rfl) ?_⟩
      unfold Capture Near; omega
  · obtain ⟨o, u, sd⟩ := two_sides hc (by omega : a = c + 1 ∨ a + 1 = c)
    have fr : Free a b e f c 6 := by unfold Free; omega
    exact Or.inl ⟨fr, w6_side (dom_push D fr) hc sd rfl (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- The king beside the pawn, unopposed, steps ahead or lets the pawn evict. -/
theorem mv_beside {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (ph : Phi j a b c)
    (bs : Beside a b c) (opp : ¬ (e = a ∧ f = 7)) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  have bs' := bs
  unfold Beside at bs'
  obtain ⟨rfl, side⟩ := bs'
  obtain ⟨o, u, sd⟩ := two_sides hc side
  have sd' := sd
  unfold Sd at sd'
  unfold Phi Ch at ph
  have hj : 2 ≤ j := by
    rcases ph with ph | ph | ph | ph | ph <;> omega
  by_cases g : Apart a 6 e f
  · have st : KingStep a 5 c 5 e f a 6 := by unfold Apart at g; unfold KingStep Near Apart; omega
    exact Or.inr ⟨j - 1, by omega, a, 6, st, w_key (dom_step D st) hc sd rfl (Or.inl rfl)
      (by unfold Capture Near; omega)⟩
  unfold Apart at g
  by_cases blk : e = c
  · have fr : Free a 5 e f c 6 := by unfold Free; omega
    exact Or.inl ⟨fr, w6_evict (dom_push D fr) hc sd rfl rfl blk (by omega)⟩
  · have st : KingStep a 5 c 5 e f c 6 := by unfold KingStep Near Apart; omega
    exact Or.inr ⟨j - 1, by omega, c, 6, st, w_c6 (dom_step D st) hc (by omega) rfl rfl⟩

set_option maxHeartbeats 4000000 in
/-- The king two files out on the last rank steps onto a key square. -/
theorem mv_u7 {j a b c e f t o u : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (hj : 1 ≤ j) (sd : Sd c t o u)
    (ha : a = u) (hb : b = 7) (nA : ¬ (e = t ∧ f = 5)) (nF : ¬ (e = c ∧ f = 6))
    (nB : ¬ (e = c ∧ f = 7)) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have sd' := sd
  unfold Sd at sd'
  refine Or.inr ⟨j - 1, by omega, ?_⟩
  by_cases g : Apart t 6 e f
  · have st : KingStep a b c 5 e f t 6 := by unfold Apart at g; unfold KingStep Near Apart; omega
    exact ⟨t, 6, st, w_key (dom_step D st) hc sd rfl (Or.inl rfl) (by unfold Capture Near; omega)⟩
  · unfold Apart at g
    have st : KingStep a b c 5 e f t 7 := by unfold KingStep Near Apart; omega
    exact ⟨t, 7, st, w_key (dom_step D st) hc sd rfl (Or.inr rfl) (by unfold Capture Near; omega)⟩

/-- The king steps beside the pawn unopposed. -/
theorem mv_sn {j a b c e f t o u : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (hj : 3 ≤ j) (sd : Sd c t o u)
    (h : SN a b c e f t) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨n, ap, op, ns⟩ := h
  have sd' := sd
  unfold Sd at sd'
  have st : KingStep a b c 5 e f t 5 := ⟨n, by omega, by omega, by omega, ap⟩
  exact Or.inr ⟨j - 1, by omega, t, 5, st, w_bes (dom_step D st) hc (by omega) sd rfl rfl op ns⟩

set_option maxHeartbeats 4000000 in
/-- The king goes behind the pawn to change sides. -/
theorem mv_behind {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (hj : 4 ≤ j)
    (h1 : Ch a b c 4 1) (h2 : ¬ (a = c ∧ b = 4)) (b1 : ¬ Bl 1 c e f) (sq : ¬ Outside 2 c e f) :
    Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Ch at h1
  unfold Bl Ch at b1
  unfold Outside at sq
  have k2 := D.1.k2
  have st : KingStep a b c 5 e f c 4 := by
    unfold KingStep Near Apart
    omega
  have keep : ¬ Capture c 4 c 5 e f := by unfold Capture Near; omega
  refine Or.inr ⟨j - 1, by omega, c, 4, st, ?_⟩
  refine w_close (dom_step D st) hc (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)))) ?_ ?_ ?_ (by omega)
    (by unfold Bl Ch; omega) keep (by omega)
  · unfold Arr Ch; omega
  · unfold Ch; omega
  · unfold Beside; omega

set_option maxHeartbeats 4000000 in
/-- The lone king is on the far side: after the push it cannot stop the king reaching the
promotion square. -/
theorem mv_sp {j a b c e f t o u v : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (hv : (o = c + 1 ∧ v = c + 2) ∨ (o + 1 = c ∧ v + 2 = c))
    (h : SP a b c e f t o v) (nk : ¬ Key5 a b c) (nb : ¬ Beside a b c) (nu : ¬ (a = u ∧ b = 7))
    (ns : ¬ SN a b c e f t) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  have k3 := D.1.k3
  have k4 := D.k4
  obtain ⟨h1, h2, h3⟩ := h
  have sd' := sd
  unfold Sd at sd'
  unfold Ch at h1
  unfold Key5 at nk
  unfold Beside at nb
  unfold SN Near Apart at ns
  have fr : Free a b e f c 6 := by unfold Free; omega
  have keep : ¬ Capture a b c 6 e f := by unfold Capture Near; omega
  refine Or.inl ⟨fr, keep, ⟨e, f - 1, by unfold WeakStep Near Apart Att; omega⟩, ?_⟩
  intro x y st g
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  have s7 := st.k7
  have s8 := st.k8
  obtain ⟨-, -, q | q | q⟩ := g
  · unfold Block7 Near at q; omega
  · unfold SideL Within1 at q; omega
  · unfold SideR Within1 at q; omega

set_option maxHeartbeats 4000000 in
/-- The lone king is two files out and the king within reach: it heads for the pawn. -/
theorem mv_far {j a b c e f x y : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (ph : Ch x y c 4 (j - 4))
    (hj : 5 ≤ j) (st : KingStep a b c 5 e f x y) (hu : e = c + 2 ∨ e + 2 = c)
    (a1 : ¬ Arr 1 x y c) (p2 : Ch x y c 5 2) (nb : ¬ Beside x y c) (y7 : y ≠ 7)
    (ns : ¬ (c = 2 ∧ e = 0 ∧ f = 7 ∧ x = 1 ∧ y = 5)) : Mv j a b c e f := by
  have Dn := dom_step D st
  refine Or.inr ⟨j - 1, by omega, x, y, st, ?_⟩
  have keep : ¬ Capture x y c 5 e f := by
    unfold Capture Near; omega
  refine w_close Dn hc (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩)))) a1 p2 nb y7 (by unfold Bl Ch; omega) keep ns
  have : j - 1 - 3 = j - 4 := by omega
  rw [this]; exact ph

end EndgameChess.Rules.KPK.Coord
