import EndgameChess.Rules.KPK.Coord.KnSix

/-! Wins with a knight pawn on the sixth rank, outside the guard. This is the argument of
`SixWin`, `SixMove`, `SixCover` and `SixMain` repeated for every non-rook file, with the
knight-file differences: the lone king in the corner is stalemated by a king on `c7` or
`c8`, and the two corner draws of `KnSix` belong to the guard. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK
namespace Kn

/-- The sixth-rank draw region, with the two corner draws on the knight file. -/
def S5 (a b c e f : Nat) : Prop :=
  Coord.S5 a b c e f ∨ (c = 1 ∧ e = 0 ∧ f = 7 ∧ ((a = 2 ∧ b = 5) ∨ (a = 3 ∧ b = 7)))

theorem s5_old {a b c e f : Nat} (n : ¬ S5 a b c e f) : ¬ Coord.S5 a b c e f :=
  fun h => n (Or.inl h)

/-- Side predicate that also serves a knight pawn: on its short side the file two out is
a dummy off the board. -/
def Sd (c t o u : Nat) : Prop :=
  (t = c + 1 ∧ o + 1 = c ∧ u = c + 2) ∨ (t + 1 = c ∧ o = c + 1 ∧ (u + 2 = c ∨ (c = 1 ∧ u = 9)))

theorem sd_left {c : Nat} (hc : 1 ≤ c) : ∃ ul, Sd c (c - 1) (c + 1) ul := by
  by_cases c1 : c = 1
  · exact ⟨9, Or.inr ⟨by omega, rfl, Or.inr ⟨c1, rfl⟩⟩⟩
  · exact ⟨c - 2, Or.inr ⟨by omega, rfl, Or.inl (by omega)⟩⟩


/-- A push with the king beside or ahead of the pawn. -/
theorem w6_side {a b c e f t o u : Nat} (D : Dom a b c 6 e f) (hc : 1 ≤ c) (sd : Sd c t o u)
    (ha : a = t) (hb : b = 6 ∨ b = 7) : W6 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  have r : R6 a b c 6 := by
    unfold Sd at sd
    unfold R6
    omega
  have keep : ¬ Capture a b c 6 e f := by
    unfold Sd at sd
    unfold Capture Near
    omega
  refine ⟨keep, key_reply D (by omega) keep (Or.inr r), ?_⟩
  intro x y st h
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  have a7 := st.k7
  unfold Sd at sd
  obtain ⟨-, -, q | q | q⟩ := h
  · unfold Block7 at q; omega
  · unfold SideL Within1 at q; omega
  · unfold SideR Within1 at q; omega

/-- A pawn the lone king cannot catch: every reply stays off the top guard squares. -/
theorem w6_run {a b c e f : Nat} (D : Dom a b c 6 e f) (hc : 1 ≤ c) (out : Outside 2 c e f) :
    W6 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Outside at out
  have keep : ¬ Capture a b c 6 e f := by
    unfold Capture Near
    omega
  refine ⟨keep, weak_reply D (by omega) keep, ?_⟩
  intro x y st h
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  obtain ⟨-, -, q | q | q⟩ := h
  · unfold Block7 at q; omega
  · unfold SideL at q; omega
  · unfold SideR at q; omega

/-- A key square ends the guard. -/
theorem nd_key {a b c e f : Nat} (k : Key5 a b c) : ¬ S5 a b c e f := by
  rintro (h | ⟨rfl, -, -, h⟩)
  · exact h.1 k
  · unfold Key5 at k
    omega

/-- A king beside the pawn is stopped only directly opposite. -/
theorem nd_beside {a b c e f : Nat} (k : Beside a b c) (no : ¬ (e = a ∧ f = 7))
    (no2 : ¬ (c = 1 ∧ e = 0 ∧ f = 7 ∧ a = 2)) : ¬ S5 a b c e f := by
  rintro (⟨-, -, -, -, ⟨-, h1, h2⟩ | ⟨nb, -⟩⟩ | ⟨h1, h2, h3, h4⟩)
  · exact no ⟨h1, h2⟩
  · exact nb k
  · unfold Beside at k
    omega

set_option maxHeartbeats 4000000 in
/-- A king close to the pawn beats a lone king not yet on a blockade square. -/
theorem nd_close {x y c p q : Nat} (hc : 1 ≤ c) (a1 : ¬ Arr 1 x y c) (p2 : Ch x y c 5 2)
    (nbs : ¬ Beside x y c) (y7 : y ≠ 7 ∨ q ≠ 5) (b0 : ¬ Bl 0 c p q)
    (nx : ¬ (c = 1 ∧ p = 0 ∧ q = 7 ∧ x = 3 ∧ y = 7)) : ¬ S5 x y c p q := by
  rintro (⟨k, -, -, -, ⟨bs, h1, h2⟩ | ⟨nb, h⟩⟩ | ⟨h1, h2, h3, h4⟩)
  rotate_right
  · unfold Beside at nbs
    omega
  · exact nbs bs
  · have a2 : ¬ Arr 2 x y c := by
      unfold Arr Ch at a1 ⊢
      omega
    unfold Ch at p2
    rcases h with A | ⟨B, R⟩ | ⟨B, R⟩ | ⟨B, R⟩ | ⟨-, -, -, R⟩ | ⟨-, F⟩ | ⟨-, F⟩ | ⟨-, F⟩
    · omega
    · exact b0 B
    · exact a1 R
    · exact a2 R
    · exact a1 R
    · exact F (by unfold Ch; omega)
    · exact F (by unfold Ch; omega)
    · exact F (by unfold Ch; omega)

/-- Lone king to move on the sixth rank: no capture, a reply, and no reply reaches the guard. -/
def W5win (j a b c e f : Nat) : Prop :=
  Phi j a b c ∧ ¬ Capture a b c 5 e f ∧ (∃ x y, WeakStep a b c 5 e f x y) ∧
    ∀ x y, WeakStep a b c 5 e f x y → ¬ S5 a b c x y

set_option maxHeartbeats 4000000 in
/-- The lone king has a move unless it is stalemated next to the king and the sixth-rank pawn. -/
theorem six_reply {a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 1 ≤ c) (keep : ¬ Capture a b c 5 e f)
    (no : ¬ (c = 2 ∧ e = 0 ∧ f = 7 ∧ a = 1 ∧ b = 5))
    (no2 : ¬ (c = 1 ∧ e = 0 ∧ f = 7 ∧ a = 2 ∧ 6 ≤ b)) : ∃ x y, WeakStep a b c 5 e f x y := by
  by_cases top : f ≤ 6 ∨ 5 ≤ 4 ∨ c + 2 < e ∨ e + 2 < c
  · exact weak_reply D top keep
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  apply Classical.byContradiction
  intro none
  have t (x y : Nat) : ¬ WeakStep a b c 5 e f x y := fun s => none ⟨x, y, s⟩
  have h1 := t (e + 1) f
  have h2 := t (e - 1) f
  have h4 := t e (f - 1)
  have h5 := t (e + 1) (f - 1)
  have h6 := t (e - 1) (f - 1)
  unfold WeakStep Near Apart Att at h1 h2 h4 h5 h6
  have z : f = 7 := by omega
  subst z
  rcases Nat.lt_trichotomy e c with g | g | g <;> omega

/-- The king steps beside the pawn on the side `t` unopposed. -/
def SN (a b c e f t : Nat) : Prop :=
  Near a b t 5 ∧ Apart t 5 e f ∧ ((e = t ∧ f = 7) ∨ ¬ Near e f t 7) ∧
    ¬ (c = 2 ∧ t = 1 ∧ e = 0 ∧ f = 7)

/-- The king is next to a key square and the lone king on the far side of the pawn. -/
def SP (a b c e f t o u : Nat) : Prop := Ch a b t 6 1 ∧ (e = o ∨ e = u) ∧ 6 ≤ f

/-- The classes left once the king is not on a key, beside the pawn or two files out on
the last rank. -/
def Step5 (a b c e f : Nat) : Prop :=
  SN a b c e f (c + 1) ∨ SN a b c e f (c - 1) ∨ SP a b c e f (c + 1) (c - 1) (c - 2) ∨
    SP a b c e f (c - 1) (c + 1) (c + 2) ∨ (Ch a b c 4 1 ∧ ¬ (a = c ∧ b = 4) ∧ ¬ Bl 1 c e f) ∨
    ((e = c + 2 ∨ e + 2 = c) ∧ ¬ Arr 2 a b c)



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

theorem w_key {j a b c e f t o u : Nat} (D : Dom a b c 5 e f) (hc : 1 ≤ c) (sd : Sd c t o u)
    (ha : a = t) (hb : b = 6 ∨ b = 7) (keep : ¬ Capture a b c 5 e f)
    (ns : ¬ (c = 1 ∧ e = 0 ∧ f = 7 ∧ a = 2)) : W5win j a b c e f := by
  unfold Sd at sd
  have nk : Key5 a b c := by unfold Key5; omega
  refine ⟨Or.inl ⟨by omega, by omega⟩, keep, key_reply D (by omega) keep
    (Or.inl ⟨by unfold Cl; omega, by omega, by omega, by unfold Stale; omega⟩), ?_⟩
  exact fun x y _ => nd_key nk

theorem w_c6 {j a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 1 ≤ c) (hj : 1 ≤ j)
    (ha : a = c) (hb : b = 6) : W5win j a b c e f := by
  have nk : Key5 a b c := by unfold Key5; omega
  have keep : ¬ Capture a b c 5 e f := by unfold Capture Near; omega
  refine ⟨Or.inr (Or.inl ⟨hj, Or.inl ⟨ha, by omega⟩⟩), keep, key_reply D (by omega) keep
    (Or.inl ⟨by unfold Cl; omega, by omega, by omega, by unfold Stale; omega⟩), ?_⟩
  exact fun x y _ => nd_key nk

theorem w_bes {j a b c e f t o u : Nat} (D : Dom a b c 5 e f) (hc : 1 ≤ c) (hj : 2 ≤ j) (sd : Sd c t o u)
    (ha : a = t) (hb : b = 5) (opp : (e = t ∧ f = 7) ∨ ¬ Near e f t 7)
    (ns : ¬ (c = 2 ∧ t = 1 ∧ e = 0 ∧ f = 7))
    (k4 : ¬ (f = 6 ∧ (e = c + 1 ∨ e + 1 = c))) : W5win j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Sd at sd
  have bs : Beside a b c := by unfold Beside; omega
  have keep : ¬ Capture a b c 5 e f := by unfold Capture Near; omega
  refine ⟨Or.inr (Or.inr (Or.inl ⟨hj, bs⟩)), keep, six_reply D hc keep (by omega) (by omega), ?_⟩
  intro x y st
  have k5 := st.k5
  obtain ⟨n, -, -⟩ := st
  unfold Near at n opp
  refine nd_beside bs (by omega) ?_
  rintro ⟨h1, h2, h3, h4⟩
  omega

theorem w_close {j a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 1 ≤ c) (ph : Phi j a b c)
    (a1 : ¬ Arr 1 a b c) (p2 : Ch a b c 5 2) (nb : ¬ Beside a b c) (y7 : b ≠ 7) (b1 : ¬ Bl 1 c e f)
    (keep : ¬ Capture a b c 5 e f) (ns : ¬ (c = 2 ∧ e = 0 ∧ f = 7 ∧ a = 1 ∧ b = 5)) :
    W5win j a b c e f := by
  refine ⟨ph, keep, six_reply D hc keep ns (by unfold Bl Ch at b1; omega), ?_⟩
  intro x y st
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  refine nd_close hc a1 p2 nb (Or.inl y7) ?_ (by omega)
  unfold Bl Ch at b1 ⊢
  omega

set_option maxHeartbeats 4000000 in
/-- The pawn reaches the seventh with the lone king forced off the promotion square. -/
theorem w6_evict {a b c e f t o u : Nat} (D : Dom a b c 6 e f) (hc : 1 ≤ c) (sd : Sd c t o u)
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

theorem two_sides {c a : Nat} (hc : 1 ≤ c) (h : a = c + 1 ∨ a + 1 = c) : ∃ o u, Sd c a o u := by
  rcases h with h | h
  · exact ⟨c - 1, c + 2, Or.inl ⟨h, by omega, rfl⟩⟩
  · by_cases c1 : c = 1
    · exact ⟨c + 1, 9, Or.inr ⟨h, rfl, Or.inr ⟨c1, rfl⟩⟩⟩
    · exact ⟨c + 1, c - 2, Or.inr ⟨h, rfl, Or.inl (by omega)⟩⟩

set_option maxHeartbeats 4000000 in
/-- The king is ahead of the pawn. -/
theorem mv_ahead {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (ph : Phi j a b c)
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
      refine ⟨c + 1, 6, st, w_key (dom_step D st) hc sd rfl (Or.inl rfl) ?_ (by omega)⟩
      unfold Capture Near; omega
    · obtain ⟨o, u, sd⟩ := two_sides (a := c - 1) hc (Or.inr (by omega))
      unfold Apart at g
      have st : KingStep a b c 5 e f (c - 1) 6 := by unfold KingStep Near Apart; omega
      refine ⟨c - 1, 6, st, w_key (dom_step D st) hc sd rfl (Or.inl rfl) ?_ (by omega)⟩
      unfold Capture Near; omega
  · obtain ⟨o, u, sd⟩ := two_sides hc (by omega : a = c + 1 ∨ a + 1 = c)
    have fr : Free a b e f c 6 := by unfold Free; omega
    exact Or.inl ⟨fr, w6_side (dom_push D fr) hc sd rfl (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- The king beside the pawn, unopposed, steps ahead or lets the pawn evict. -/
theorem mv_beside {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (ph : Phi j a b c)
    (bs : Beside a b c) (opp : ¬ (e = a ∧ f = 7))
    (na8 : ¬ (c = 1 ∧ e = 0 ∧ f = 7 ∧ a = 2)) : Mv j a b c e f := by
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
      (by unfold Capture Near; omega) (by omega)⟩
  unfold Apart at g
  by_cases blk : e = c
  · have fr : Free a 5 e f c 6 := by unfold Free; omega
    exact Or.inl ⟨fr, w6_evict (dom_push D fr) hc sd rfl rfl blk (by omega)⟩
  · have st : KingStep a 5 c 5 e f c 6 := by unfold KingStep Near Apart; omega
    exact Or.inr ⟨j - 1, by omega, c, 6, st, w_c6 (dom_step D st) hc (by omega) rfl rfl⟩

set_option maxHeartbeats 4000000 in
/-- The king two files out on the last rank steps onto a key square. -/
theorem mv_u7 {j a b c e f t o u : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (hj : 1 ≤ j) (sd : Sd c t o u)
    (ha : a = u) (hb : b = 7) (nA : ¬ (e = t ∧ f = 5)) (nF : ¬ (e = c ∧ f = 6))
    (nB : ¬ (e = c ∧ f = 7)) (na8 : ¬ (c = 1 ∧ e = 0 ∧ f = 7)) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have sd' := sd
  unfold Sd at sd'
  refine Or.inr ⟨j - 1, by omega, ?_⟩
  by_cases g : Apart t 6 e f
  · have st : KingStep a b c 5 e f t 6 := by unfold Apart at g; unfold KingStep Near Apart; omega
    exact ⟨t, 6, st, w_key (dom_step D st) hc sd rfl (Or.inl rfl) (by unfold Capture Near; omega)
      (by omega)⟩
  · unfold Apart at g
    have st : KingStep a b c 5 e f t 7 := by unfold KingStep Near Apart; omega
    exact ⟨t, 7, st, w_key (dom_step D st) hc sd rfl (Or.inr rfl) (by unfold Capture Near; omega)
      (by omega)⟩

/-- The king steps beside the pawn unopposed. -/
theorem mv_sn {j a b c e f t o u : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (hj : 3 ≤ j) (sd : Sd c t o u)
    (h : SN a b c e f t) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨n, ap, op, ns⟩ := h
  have sd' := sd
  unfold Sd at sd'
  have st : KingStep a b c 5 e f t 5 := ⟨n, by omega, by omega, by omega, ap⟩
  exact Or.inr ⟨j - 1, by omega, t, 5, st, w_bes (dom_step D st) hc (by omega) sd rfl rfl op ns
    (by have := D.k4; omega)⟩

set_option maxHeartbeats 4000000 in
/-- The king goes behind the pawn to change sides. -/
theorem mv_behind {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (hj : 4 ≤ j)
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
theorem mv_sp {j a b c e f t o u v : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (sd : Sd c t o u)
    (hv : (o = c + 1 ∧ v = c + 2) ∨ (o + 1 = c ∧ v + 2 = c) ∨ (c = 1 ∧ o = 0 ∧ v = 0))
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
theorem mv_far {j a b c e f x y : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (ph : Ch x y c 4 (j - 4))
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



set_option maxHeartbeats 4000000 in
/-- The lone king next to the pawn's file: the king steps beside the pawn. -/
theorem cover_t {a b c e f t o u : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (sd : Sd c t o u)
    (he : e = t) (hf : f = 5 ∨ f = 7) (a1 : ¬ Arr 1 a b c) (k : ¬ Key5 a b c) (bs : ¬ Beside a b c)
    (u7 : ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7)) (top : f = 5 → ¬ (a = u ∧ b = 7)) :
    SN a b c e f t ∨ SN a b c e f o := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7'⟩ := D.bounds
  have k1 : Apart a b e f := D.1.k1
  have a1' : Ch a b (c + 1) 5 1 ∨ Ch a b (c + 1) 6 1 ∨ Ch a b (c - 1) 5 1 ∨ Ch a b (c - 1) 6 1 := by
    apply Classical.byContradiction
    intro q
    exact a1 ⟨fun g => q (Or.inl g), fun g => q (Or.inr (Or.inl g)), fun g => q (Or.inr (Or.inr (Or.inl g))),
      fun g => q (Or.inr (Or.inr (Or.inr g)))⟩
  clear a1
  unfold Ch at a1'
  unfold Key5 at k
  unfold Beside at bs
  unfold Apart at k1
  have ky : b ≤ 5 ∨ ¬ (a ≤ c + 1 ∧ c ≤ a + 1) := by omega
  have by' : b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  clear k
  have sd' := sd
  unfold Sd at sd'
  by_cases g : f = 7 ∧ Near a b t 5
  · exact Or.inl ⟨g.2, by unfold Apart; omega, Or.inl ⟨he, g.1⟩, by omega⟩
  refine Or.inr ⟨?_, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
  unfold Near at g ⊢
  rcases sd' with s1 | s1 <;> rcases hf with rfl | rfl <;>
    rcases a1' with h | h | h | h <;> omega

/-- Every position outside the guard, the key squares, the squares beside the pawn and the
far last-rank squares, with the lone king in the pawn's square, is in a strategy class. -/
theorem step5_cover {a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (n' : ¬ S5 a b c e f)
    (sq : ¬ Outside 2 c e f) (k : ¬ Key5 a b c) (bs : ¬ Beside a b c)
    (u7 : ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7)) : Step5 a b c e f := by
  have n : ¬ Coord.S5 a b c e f := s5_old n'
  obtain ⟨u1, u2, u3, u4, u5, u6, u7'⟩ := D.bounds
  have k3 := D.1.k3
  have k4 := D.k4
  unfold Outside at sq
  have h1 : e ≤ c + 2 := by omega
  have h2 : c ≤ e + 2 := by omega
  have h3 : 5 ≤ f := by omega
  have bk0 : Bl 0 c e f → ¬ Arr 0 a b c := fun b r => n (s5_bl0 b r k bs h1 h2 h3)
  have bk1 : Bl 1 c e f → ¬ Arr 1 a b c := fun b r => n (s5_bl1 b r k bs h1 h2 h3)
  by_cases two : e = c + 2 ∨ e + 2 = c
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨two, fun r => n ?_⟩))))
    exact ⟨k, h1, h2, h3, Or.inr ⟨bs, Or.inr (Or.inr (Or.inr (Or.inl ⟨by unfold Bl Ch; omega, r⟩)))⟩⟩
  by_cases mid : e = c
  · exfalso
    apply bk0 (by unfold Bl Ch; omega)
    unfold Key5 at k
    unfold Beside at bs
    unfold Arr Ch
    omega
  have sdr : Sd c (c + 1) (c - 1) (c + 2) := Or.inl ⟨rfl, by omega, rfl⟩
  obtain ⟨ul, sdl⟩ := sd_left hc
  have a1 : ¬ Arr 1 a b c := bk1 (by unfold Bl Ch; omega)
  have row : f = 5 ∨ f = 7 := by omega
  by_cases right : e = c + 1
  · rcases cover_t D hc sdr right row a1 k bs u7 (fun _ q => u7 ⟨Or.inl q.1, q.2⟩) with q | q
    · exact Or.inl q
    · exact Or.inr (Or.inl q)
  · rcases cover_t D hc sdl (by omega) row a1 k bs u7 (fun _ q => by
      have s := sdl
      unfold Sd at s
      exact u7 ⟨Or.inr (by omega), q.2⟩) with q | q
    · exact Or.inr (Or.inl q)
    · exact Or.inl q



set_option maxHeartbeats 4000000 in
/-- A far king heads diagonally for the square behind the pawn. -/
theorem mv_step {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (ph : Ch a b c 4 (j - 3))
    (hj : 3 ≤ j) (far : ¬ Ch a b c 4 1) (hu : e = c + 2 ∨ e + 2 = c) (hf : 5 ≤ f) (a2 : ¬ Arr 2 a b c)
    (n1 : ¬ SN a b c e f (c + 1)) (n2 : ¬ SN a b c e f (c - 1))
    (nk : ¬ Key5 a b c) (nb : ¬ Beside a b c) (nu : ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7))
    (hs : Arr 1 a b c → ¬ (f = 5 ∧ ((e = c + 2 ∧ c + 2 ≤ a) ∨ (e + 2 = c ∧ a + 2 ≤ c)) ∧ (b = 3 ∨ b = 7))) :
    Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  have a2' : Ch a b (c + 1) 5 2 ∨ Ch a b (c + 1) 6 2 ∨ Ch a b (c - 1) 5 2 ∨ Ch a b (c - 1) 6 2 := by
    apply Classical.byContradiction
    intro q
    exact a2 ⟨fun g => q (Or.inl g), fun g => q (Or.inr (Or.inl g)), fun g => q (Or.inr (Or.inr (Or.inl g))),
      fun g => q (Or.inr (Or.inr (Or.inr g)))⟩
  have same : ¬ (f = 5 ∧ ((e = c + 2 ∧ c + 2 ≤ a) ∨ (e + 2 = c ∧ a + 2 ≤ c)) ∧ (b = 3 ∨ b = 7)) := by
    intro q
    apply hs _ q
    unfold Arr Ch
    omega
  have r6 : ¬ (a = c + 2 ∧ b = 6 ∧ e + 2 = c) := by
    rintro ⟨h1, h2, h3⟩
    exact n1 ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
  have l6 : ¬ (a + 2 = c ∧ b = 6 ∧ e = c + 2) := by
    rintro ⟨h1, h2, h3⟩
    exact n2 ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
  clear hs n1 n2 a2
  obtain ⟨x, hx⟩ : ∃ x, (c + 2 ≤ a ∧ x + 1 = a) ∨ (a + 2 ≤ c ∧ x = a + 1) ∨ (a ≤ c + 1 ∧ c ≤ a + 1 ∧ x = a) := by
    by_cases g : c + 2 ≤ a
    · exact ⟨a - 1, Or.inl ⟨g, by omega⟩⟩
    · by_cases g2 : a + 2 ≤ c
      · exact ⟨a + 1, Or.inr (Or.inl ⟨g2, rfl⟩)⟩
      · exact ⟨a, Or.inr (Or.inr ⟨by omega, by omega, rfl⟩)⟩
  obtain ⟨y, hy⟩ : ∃ y, (b ≤ 3 ∧ y = b + 1) ∨ (5 ≤ b ∧ y + 1 = b) ∨ (b = 4 ∧ y = 4) := by
    by_cases g : b ≤ 3
    · exact ⟨b + 1, Or.inl ⟨g, rfl⟩⟩
    · by_cases g2 : 5 ≤ b
      · exact ⟨b - 1, Or.inr (Or.inl ⟨g2, by omega⟩)⟩
      · exact ⟨4, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩
  unfold Ch at ph far a2'
  unfold Key5 at nk
  unfold Beside at nb
  have ax : a ≤ x + 1 ∧ x ≤ a + 1 := by
    clear same r6 l6 nk nb nu ph far a2' k1 k3 k4 hy
    omega
  have ay : b ≤ y + 1 ∧ y ≤ b + 1 := by
    clear same r6 l6 nk nb nu ph far a2' k1 k3 k4 hx
    omega
  have ne : ¬ (a = x ∧ b = y) := by
    clear same r6 l6 nk nb nu ph a2' k1 k3 k4
    omega
  have ap : Apart x y e f := by
    clear r6 l6 ph k3 k4
    unfold Apart
    rcases hu with g | g <;> rcases a2' with q | q | q | q <;> omega
  have np : ¬ (x = c ∧ y = 5) := by
    clear same r6 l6 nb nu ph far a2' k1 k3 k4 ap
    omega
  have st : KingStep a b c 5 e f x y :=
    ⟨⟨ax.1, ax.2, ay.1, ay.2, ne⟩, by clear same r6 l6 nk nb nu ph far a2' k1 k3 k4; omega,
      by clear same r6 l6 nk nb nu ph far a2' k1 k3 k4; omega, np, ap⟩
  have mp : Ch x y c 4 (j - 4) := by
    clear same r6 l6 nk nb nu a2' k1 k3 k4 ap st np
    unfold Ch; omega
  have a1 : ¬ Arr 1 x y c := by
    clear same r6 l6 nk nb nu ph far k1 k3 k4 ap st np mp
    intro r
    obtain ⟨r1, r2, r3, r4⟩ := r
    unfold Ch at r1 r2 r3 r4
    rcases a2' with q | q | q | q <;> omega
  have p2 : Ch x y c 5 2 := by
    clear same r6 l6 nk nb nu ph far k1 k3 k4 ap st np mp a1
    unfold Ch; rcases a2' with q | q | q | q <;> omega
  have bx : ¬ Beside x y c := by
    clear same nu ph far k3 k4 ap st np mp a1 p2 a2' nb ax ay ne
    unfold Beside
    rintro ⟨g1, g2⟩
    have b6 : b = 6 := by
      clear r6 l6 nk k1 g2 hx hu
      omega
    subst b6
    have side : c + 2 ≤ a ∨ a + 2 ≤ c := by omega
    rcases hu with g | g <;> rcases side with g3 | g3 <;> rcases g2 with g4 | g4 <;> omega
  have y7 : y ≠ 7 := by
    clear same r6 l6 nk nb nu ph far a2' k1 k3 k4 ap st np mp a1 p2 bx
    omega
  have j5 : 5 ≤ j := by
    clear same r6 l6 nk nb nu a2' k1 k3 k4 ap st np mp a1 p2 bx hx hy
    unfold Ch at *
    omega
  refine mv_far D hc mp j5 st hu a1 p2 bx y7 ?_
  rintro ⟨g1, g2, g3, g4, g5⟩
  exact bx ⟨g5, Or.inr (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- Every sixth-rank position outside the guard has its planned move. -/
theorem six_move {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 1 ≤ c) (n' : ¬ S5 a b c e f)
    (ph : Phi j a b c) (cover : ¬ Outside 2 c e f → ¬ Key5 a b c → ¬ Beside a b c →
      ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7) → Step5 a b c e f) : Mv j a b c e f := by
  have n : ¬ Coord.S5 a b c e f := s5_old n'
  have nx : ¬ (c = 1 ∧ e = 0 ∧ f = 7 ∧ ((a = 2 ∧ b = 5) ∨ (a = 3 ∧ b = 7))) :=
    fun h => n' (Or.inr h)
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  by_cases key : (a = c + 1 ∨ a + 1 = c ∨ a = c) ∧ 6 ≤ b
  · exact mv_ahead D hc ph key.1 key.2
  have nk : ¬ Key5 a b c := by unfold Key5; omega
  by_cases sq : Outside 2 c e f
  · have s' := sq
    unfold Outside at s'
    have fr : Free a b e f c 6 := by unfold Free; omega
    exact Or.inl ⟨fr, w6_run (dom_push D fr) hc sq⟩
  have s' := sq
  unfold Outside at s'
  by_cases bs : Beside a b c
  · refine mv_beside D hc ph bs ?_ (by unfold Beside at bs; omega)
    rintro ⟨h1, h2⟩
    exact n ⟨nk, by omega, by omega, by omega, Or.inl ⟨bs, h1, h2⟩⟩
  by_cases top : (a = c + 2 ∨ a + 2 = c) ∧ b = 7
  · have r0 : Arr 0 a b c := by unfold Arr Ch; omega
    have hj : 1 ≤ j := by
      unfold Phi Ch at ph
      rcases ph with q | q | q | q | q <;> omega
    have nF : ¬ (e = c ∧ f = 6) := by
      rintro ⟨rfl, rfl⟩
      exact n (s5_bl0 (Or.inl (by unfold Ch; omega)) r0 nk bs (by omega) (by omega) (by omega))
    have nB : ¬ (e = c ∧ f = 7) := by
      rintro ⟨rfl, rfl⟩
      exact n (s5_bl0 (Or.inr (by unfold Ch; omega)) r0 nk bs (by omega) (by omega) (by omega))
    have nA : (a = c + 2 → ¬ (e = c + 1 ∧ f = 5)) ∧ (a + 2 = c → ¬ (e + 1 = c ∧ f = 5)) := by
      constructor
      · rintro h ⟨h1, h2⟩
        exact n ⟨nk, by omega, by omega, by omega, Or.inr ⟨bs, Or.inl ⟨h2, Or.inl ⟨h1, h⟩, top.2⟩⟩⟩
      · rintro h ⟨h1, h2⟩
        exact n ⟨nk, by omega, by omega, by omega, Or.inr ⟨bs, Or.inl ⟨h2, Or.inr ⟨h1, h⟩, top.2⟩⟩⟩
    rcases top with ⟨h | h, hb⟩
    · exact mv_u7 D hc hj (t := c + 1) (o := c - 1) (u := c + 2) (Or.inl ⟨rfl, by omega, rfl⟩) h hb (nA.1 h) nF nB
        (by omega)
    · exact mv_u7 D hc hj (t := c - 1) (o := c + 1) (u := c - 2) (Or.inr ⟨by omega, rfl, by omega⟩) (by omega) hb
        (fun q => nA.2 h ⟨by omega, q.2⟩) nF nB (by omega)
  have rest : 3 ≤ j ∧ Ch a b c 4 (j - 3) := by
    unfold Phi at ph
    rcases ph with q | q | q | q | q
    · omega
    · omega
    · exact absurd q.2 bs
    · refine ⟨q.1, ?_⟩
      unfold Ch; omega
    · exact q
  obtain ⟨hj3, ph3⟩ := rest
  have sdr : Sd c (c + 1) (c - 1) (c + 2) := Or.inl ⟨rfl, by omega, rfl⟩
  obtain ⟨ul, sdl⟩ := sd_left hc
  by_cases n1 : SN a b c e f (c + 1)
  · exact mv_sn D hc hj3 sdr n1
  by_cases n2 : SN a b c e f (c - 1)
  · exact mv_sn D hc hj3 sdl n2
  by_cases p1 : SP a b c e f (c + 1) (c - 1) (c - 2)
  · exact mv_sp D hc sdr (by omega) p1 nk bs (fun q => top ⟨Or.inl q.1, q.2⟩) n1
  by_cases p2 : SP a b c e f (c - 1) (c + 1) (c + 2)
  · exact mv_sp D hc sdl (Or.inl ⟨rfl, rfl⟩) p2 nk bs (fun q => by
      have s := sdl
      unfold Sd at s
      exact top ⟨Or.inr (by omega), q.2⟩) n2
  rcases cover sq nk bs top with h | h | h | h | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact absurd h n1
  · exact absurd h n2
  · exact absurd h p1
  · exact absurd h p2
  · exact mv_behind D hc (by unfold Ch at ph3 h1; omega) h1 h2 h3 sq
  · by_cases near : Ch a b c 4 1
    · by_cases behind : a = c ∧ b = 4
      · exfalso
        obtain ⟨rfl, rfl⟩ := behind
        rcases h1 with h1 | h1
        · apply n2
          refine ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
        · apply n1
          refine ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
      · exact mv_behind D hc (by unfold Ch at ph3 near; omega) near behind (by unfold Bl Ch; omega) sq
    · refine mv_step D hc ph3 hj3 near h1 (by omega) h2 n1 n2 nk bs top ?_
      rintro r ⟨q1, q2, q3⟩
      exact n ⟨nk, by omega, by omega, by omega, Or.inr ⟨bs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q1, q2, q3, r⟩))))⟩⟩


end Kn
end EndgameChess.Rules.KPK.Coord
