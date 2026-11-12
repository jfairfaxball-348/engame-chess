import EndgameChess.Rules.KPK.Coord.Five2

/-! Fifth-rank guard: the pawn push. After the push the lone king takes the pawn, or steps
to a blockade square of the sixth-rank guard. -/
namespace EndgameChess.Rules.KPK.Coord

/-- `u` is two files out and `w` three files out on the same side. -/
def Sw (c u w : Nat) : Prop := (u = c + 2 ∧ w = c + 3) ∨ (u + 2 = c ∧ w + 3 = c)

/-- The lone king stands strictly between the pawn's file and the king. -/
def Btw (a c e : Nat) : Prop := (c < e ∧ e < a) ∨ (e < c ∧ a < e)

/-- The races of `M4` read by side. -/
theorem m4_side {a b c e f t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (h : M4 a b c e f) :
    Rc a b c e f t 5 ∧ Rc a b c e f t 6 ∧ Rc a b c e f o 5 ∧ Rc a b c e f o 6 ∧
      ((Btw a c e ∧ (f ≤ 6 ∨ b ≤ 3)) ∨ Oc a b c e f u) := by
  obtain ⟨⟨r1, r2, r3, r4⟩, o1, o2⟩ := h
  rcases sd with ⟨rfl, ho, rfl⟩ | ⟨ht, rfl, hu⟩
  · have e1 : o = c - 1 := by omega
    subst e1
    refine ⟨r1, r2, r3, r4, ?_⟩
    rcases o1 with ⟨p, q, r⟩ | o1
    · exact Or.inl ⟨Or.inl ⟨p, q⟩, r⟩
    · exact Or.inr o1
  · have e1 : t = c - 1 := by omega
    have e2 : u = c - 2 := by omega
    subst e1 e2
    refine ⟨r3, r4, r1, r2, ?_⟩
    rcases o2 with ⟨p, q, r⟩ | o2
    · exact Or.inl ⟨Or.inr ⟨p, q⟩, r⟩
    · exact Or.inr o2

/-- The outer-file race read off at distance `n`. -/
theorem os_at {a b c e f u : Nat} (n : Nat)
    (os : (Btw a c e ∧ (f ≤ 6 ∨ b ≤ 3)) ∨ Oc a b c e f u) :
    (Btw a c e ∧ (f ≤ 6 ∨ b ≤ 3)) ∨
      ((Ch a b u 5 n ∨ Ch a b u 6 n) → (Ch e f c 5 n ∨ Ch e f c 6 n)) := by
  rcases os with q | q
  · exact Or.inl q
  · exact Or.inr (q n)

set_option maxHeartbeats 4000000 in
/-- With the lone king two files out the king is not next to any key square. -/
theorem arr1_u {a b c f t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (h : M4 a b c u f)
    (hf : 4 ≤ f) (h7 : f ≤ 7) (hb : b ≤ 7) (nk : ¬ K4 a b c) (nb : ¬ B4 a b c)
    (k1 : Apart a b u f) (k2 : ¬ (a = c ∧ b = 4)) : Arr 1 a b c := by
  obtain ⟨r1, r2, r3, r4, os⟩ := m4_side hc sd h
  have sd' := sd
  unfold Sd at sd'
  have z1 := rc1 hc (by omega) r1
  have z2 := rc1 hc (by omega) r2
  have z3 := rc1 hc (by omega) r3
  have z4 := rc1 hc (by omega) r4
  have o1 := os_at 1 os
  clear r1 r2 r3 r4 os h sd
  unfold K4 at nk
  unfold B4 at nb
  unfold Apart at k1
  unfold Btw at o1
  have n3 : ¬ Ch a b o 5 1 := by
    intro g
    have w := z3.resolve_left (fun n => n g)
    clear z1 z2 z3 z4 o1
    unfold Ch at g w
    omega
  have n4 : ¬ Ch a b o 6 1 := by
    intro g
    have w := z4.resolve_left (fun n => n g)
    clear z1 z2 z3 z4 o1
    unfold Ch at g w
    omega
  have n2 : ¬ Ch a b t 6 1 := by
    intro g
    have w := z2.resolve_left (fun n => n g)
    clear z1 z2 z3 z4
    unfold Ch at g w n4 o1
    omega
  have n1 : ¬ Ch a b t 5 1 := by
    intro g
    have w := z1.resolve_left (fun n => n g)
    clear z1 z2 z3 z4
    unfold Ch at g w n2 o1
    omega
  clear z1 z2 z3 z4 o1
  unfold Arr
  unfold Ch at *
  omega

set_option maxHeartbeats 4000000 in
/-- With the lone king three files out the king is not within two of any key square. -/
theorem arr2_w {a b c f t o u w : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (sw : Sw c u w)
    (h : M4 a b c w f) (hf : 4 ≤ f) (h7 : f ≤ 7) (hb : b ≤ 7) (nk : ¬ K4 a b c)
    (nb : ¬ B4 a b c) (k1 : Apart a b w f) (k2 : ¬ (a = c ∧ b = 4)) : Arr 2 a b c := by
  obtain ⟨-, -, r3, r4, os⟩ := m4_side hc sd h
  have sd' := sd
  unfold Sd at sd'
  unfold Sw at sw
  have p5 := r3 2
  have p6 := rc2 hc (by omega) r4
  have o2 := os_at 2 os
  clear r3 r4 os h sd
  unfold K4 at nk
  unfold B4 at nb
  unfold Apart at k1
  unfold Btw at o2
  have n4 : ¬ Ch a b o 6 2 := by
    intro g
    have w := p6.resolve_left (fun n => n g)
    clear p5 p6 o2
    unfold WR Ch at w
    omega
  have nu : ((c < w ∧ w < a) ∨ (w < c ∧ a < w)) ∨ (¬ Ch a b u 5 2 ∧ ¬ Ch a b u 6 2) := by
    clear p5 p6
    rcases o2 with q | q
    · exact Or.inl q.1
    · right
      constructor <;> intro g
      · have w' := q (Or.inl g)
        unfold Ch at w'
        omega
      · have w' := q (Or.inr g)
        unfold Ch at w'
        omega
  have n3 : ¬ Ch a b o 5 2 := by
    intro g
    clear p6 o2
    unfold KR WR Thru Cross Hit at p5
    unfold Ch at *
    omega
  clear p5 p6 o2
  unfold Arr
  unfold Ch at *
  omega

theorem s5_bl2 {x y c e f : Nat} (b0 : Bl 2 c e f) (r : Arr 2 x y c) (k : ¬ Key5 x y c)
    (nb : ¬ Beside x y c) (h1 : e ≤ c + 2) (h2 : c ≤ e + 2) (h3 : 5 ≤ f) : S5 x y c e f :=
  ⟨k, h1, h2, h3, Or.inr ⟨nb, Or.inr (Or.inr (Or.inr (Or.inl ⟨b0, r⟩)))⟩⟩

set_option maxHeartbeats 4000000 in
/-- Two files out the lone king steps next to the pawn's file. -/
theorem push_u {a b c t o u f : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sd : Sd c t o u) (hf : 4 ≤ f)
    (h7 : f ≤ 7) (hb : b ≤ 7) (A : Arr 1 a b c) : W5 a b c u f := by
  have A' := A
  unfold Arr Ch at A'
  unfold Sd at sd
  by_cases g : f ≤ 5
  · exact Or.inr ⟨t, 5, by ws, s5_bl1 (Or.inl (by unfold Ch; omega)) A (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩
  · exact Or.inr ⟨t, 7, by ws, s5_bl1 (Or.inr (by unfold Ch; omega)) A (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- Three files out it steps to the file two out. -/
theorem push_w {a b c u w f : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sw : Sw c u w) (hf : 4 ≤ f)
    (h7 : f ≤ 7) (A : Arr 2 a b c) : W5 a b c w f := by
  have A' := A
  unfold Arr Ch at A'
  unfold Sw at sw
  by_cases g : f = 4
  · exact Or.inr ⟨u, 5, by ws, s5_bl2 (Or.inl (by unfold Ch; omega)) A (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩
  · exact Or.inr ⟨u, 6, by ws, s5_bl2 (Or.inl (by unfold Ch; omega)) A (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- On the promotion square's file the lone king steps down to the blockade. -/
theorem push_c7 {a b c : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (ha : a ≤ 7) (hb : b ≤ 7)
    (nk : ¬ K4 a b c) (k1 : Apart a b c 7) (fr : ¬ (a = c ∧ b = 5)) : W5 a b c c 7 := by
  unfold K4 at nk
  unfold Apart at k1
  exact Or.inr ⟨c, 6, by ws, s5_bl0 (Or.inl (by unfold Ch; omega)) (by ar) (by kk) (by bs)
    (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- Next to the promotion square the lone king steps to the blockade. -/
theorem push_t7 {a b c t o u : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sd : Sd c t o u)
    (h : M4 a b c t 7) (ha : a ≤ 7) (hb : b ≤ 7) (nk : ¬ K4 a b c) (k1 : Apart a b t 7)
    (fr : ¬ (a = c ∧ b = 5)) : W5 a b c t 7 := by
  obtain ⟨-, -, -, r4, -⟩ := m4_side hc sd h
  unfold Sd at sd
  have z4 := rc1 hc (by omega) r4
  clear r4 h
  unfold Ch at z4
  unfold K4 at nk
  unfold Apart at k1
  exact Or.inr ⟨c, 6, by ws, s5_bl0 (Or.inl (by unfold Ch; omega)) (by ar) (by kk) (by bs)
    (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- Opposed kings on an outer file: the lone king steps one file inwards. -/
theorem push_op {a b c e f : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (ha : a ≤ 7) (op : Op4 a b c e f)
    (sq : Sq4 c e f) : W5 a b c e f := by
  unfold Op4 at op
  unfold Sq4 at sq
  obtain ⟨rfl, rfl, q⟩ := op
  by_cases g1 : e = c + 2
  · exact Or.inr ⟨c + 1, 5, by ws, by kk, by omega, by omega, by omega,
      Or.inr ⟨by bs, Or.inl ⟨rfl, Or.inl ⟨rfl, g1⟩, by omega⟩⟩⟩
  by_cases g2 : e + 2 = c
  · exact Or.inr ⟨c - 1, 5, by ws, by kk, by omega, by omega, by omega,
      Or.inr ⟨by bs, Or.inl ⟨rfl, Or.inr ⟨by omega, g2⟩, by omega⟩⟩⟩
  by_cases g3 : e = c + 3
  · exact Or.inr ⟨c + 2, 5, by ws, by kk, by omega, by omega, by omega,
      Or.inr ⟨by bs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, Or.inl ⟨rfl, by omega⟩, by omega, by ar⟩))))⟩⟩
  · exact Or.inr ⟨c - 2, 5, by ws, by kk, by omega, by omega, by omega,
      Or.inr ⟨by bs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, Or.inr ⟨by omega, by omega⟩, by omega, by ar⟩))))⟩⟩

/-- The lone king's side of the pawn. -/
theorem side_exists {c e : Nat} (hc : 2 ≤ c) (ne : e ≠ c) (h1 : e ≤ c + 3) (h2 : c ≤ e + 3) :
    ∃ t o u, Sd c t o u ∧ (e = t ∨ e = u ∨ Sw c u e) := by
  by_cases g : c < e
  · refine ⟨c + 1, c - 1, c + 2, Or.inl ⟨rfl, by omega, rfl⟩, ?_⟩
    unfold Sw
    omega
  · refine ⟨c - 1, c + 1, c - 2, Or.inr ⟨by omega, rfl, by omega⟩, ?_⟩
    unfold Sw
    omega

set_option maxHeartbeats 4000000 in
/-- After a push to the sixth rank the lone king has its answer in the sixth-rank guard. -/
theorem s4_push {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (h : S4 a b c e f)
    (fr : Free a b e f c 5) : W5 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 : Apart a b e f := D.1.k1
  have k2 := D.1.k2
  have k3 := D.1.k3
  have k4 := D.k4
  obtain ⟨nk, sq, rest⟩ := h
  unfold Free at fr
  rcases rest with ⟨bes, rfl, ee⟩ | ⟨nb, rest⟩
  · unfold B4 at bes
    unfold Apart at k1
    rcases ee with he | he
    · exact Or.inr ⟨c, 6, by ws, s5_bl0 (Or.inl (by unfold Ch; omega)) (by ar) (by kk) (by bs)
        (by omega) (by omega) (by omega)⟩
    · exact Or.inr ⟨c, 7, by ws, s5_bl0 (Or.inr (by unfold Ch; omega)) (by ar) (by kk) (by bs)
        (by omega) (by omega) (by omega)⟩
  have far : ¬ Near a b c 5 := by
    unfold K4 at nk
    unfold B4 at nb
    unfold Near
    omega
  by_cases touch : Near e f c 5
  · exact Or.inl ⟨touch, far⟩
  have sq' := sq
  unfold Sq4 at sq'
  rcases rest with op | m | pr | rr
  · exact push_op hc u3 u1 op sq
  · by_cases mid : e = c
    · have f7 : f = 7 := by unfold Near at touch; omega
      subst mid f7
      exact push_c7 hc u3 u1 u2 nk k1 fr.1
    obtain ⟨t, o, u, sd, ev⟩ := side_exists hc mid sq'.1 sq'.2.1
    have sd' := sd
    unfold Sd at sd'
    rcases ev with rfl | rfl | sw
    · have f7 : f = 7 := by unfold Near at touch; omega
      subst f7
      exact push_t7 hc u3 sd m u1 u2 nk k1 fr.1
    · exact push_u hc u3 sd sq'.2.2 u7 u2 (arr1_u hc sd m sq'.2.2 u7 u2 nk nb k1 k2)
    · exact push_w hc u3 sw sq'.2.2 u7 (arr2_w hc sd sw m sq'.2.2 u7 u2 nk nb k1 k2)
  · obtain ⟨n1, -, -⟩ := pr
    unfold Near at n1 touch
    omega
  · unfold Rr4 at rr
    obtain ⟨r1, rfl, r3⟩ := rr
    have sd : Sd c (c - 1) (c + 1) e := Or.inr ⟨by omega, rfl, r1⟩
    exact push_u hc u3 sd (by omega) (by omega) u2 (by unfold Arr Ch; omega)

end EndgameChess.Rules.KPK.Coord
