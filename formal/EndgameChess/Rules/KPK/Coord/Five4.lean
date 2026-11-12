import EndgameChess.Rules.KPK.Coord.Five3

/-! Fifth-rank guard: king moves. Where the lone king's default step is blocked it takes
the pawn, steps beside it, keeps the opposition on an outer file, or the race conditions
show the king could not have arrived. -/
namespace EndgameChess.Rules.KPK.Coord

theorem toward_unique {e f g h u v u' v' : Nat} (t1 : Toward e f g h u v)
    (t2 : Toward e f g h u' v') : u' = u ∧ v' = v := by
  unfold Toward at t1 t2
  omega

/-- A king next to a key square that the lone king is not next to breaks the race. -/
theorem rc1_not {a b c e f p q : Nat} (hc : 2 ≤ c) (hp : p = c + 1 ∨ p + 1 = c)
    (h : Rc a b c e f p q) (far : ¬ Ch e f p q 1) : ¬ Ch a b p q 1 :=
  fun g => (rc1 hc hp h).elim (fun n => n g) far

/-- The outer-file race when the lone king is far from the pawn's file. -/
theorem os_not {a b c e f u : Nat} (n : Nat)
    (os : (Btw a c e ∧ (f ≤ 6 ∨ b ≤ 3)) ∨ Oc a b c e f u)
    (far : ¬ Ch e f c 5 n ∧ ¬ Ch e f c 6 n) :
    (Btw a c e ∧ (f ≤ 6 ∨ b ≤ 3)) ∨ (¬ Ch a b u 5 n ∧ ¬ Ch a b u 6 n) := by
  rcases os with q | q
  · exact Or.inl q
  · exact Or.inr ⟨fun g => (q n (Or.inl g)).elim far.1 far.2,
      fun g => (q n (Or.inr g)).elim far.1 far.2⟩

/-- A race in which both kings are given relative to the pawn. -/
macro "race" : tactic =>
  `(tactic| (intro n kr; obtain ⟨k1, -⟩ := kr; unfold Ch at k1; unfold WR Cross Hit Ch; omega))

macro "ocs" : tactic =>
  `(tactic| (first
    | (unfold Ocr; first | (left; omega) | (right; intro n kr; unfold Ch at *; omega))
    | (unfold Ocl; first | (left; omega) | (right; intro n kr; unfold Ch at *; omega))))

macro "m4c" : tactic =>
  `(tactic| (refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> first | race | ocs))

set_option maxHeartbeats 4000000 in
/-- King three files out on the last rank, lone king inside it on the sixth. -/
theorem m4_w7 {c u w : Nat} (hc : 2 ≤ c) (sw : Sw c u w) : M4 w 7 c u 5 := by
  unfold Sw at sw
  rcases sw with ⟨rfl, rfl⟩ | ⟨hu, hw⟩ <;> m4c

set_option maxHeartbeats 4000000 in
theorem m4_w6 {c u w : Nat} (hc : 2 ≤ c) (sw : Sw c u w) : M4 w 6 c u 4 := by
  unfold Sw at sw
  rcases sw with ⟨rfl, rfl⟩ | ⟨hu, hw⟩ <;> m4c

set_option maxHeartbeats 4000000 in
theorem m4_x7 {c : Nat} (hc : 2 ≤ c) : M4 (c + 4) 7 c (c + 2) 6 := by m4c

set_option maxHeartbeats 4000000 in
/-- A king below the pawn and no nearer than the lone king two files out. -/
theorem m4_low {x y c u : Nat} (hc : 2 ≤ c) (hy : y ≤ 3)
    (side : (u = c + 2 ∧ u ≤ x) ∨ (u + 2 = c ∧ x ≤ u)) : M4 x y c u 6 := by
  rcases side with ⟨rfl, hx⟩ | ⟨hu, hx⟩ <;> m4c

macro "w4s" : tactic => `(tactic| (unfold WeakStep Near Apart Att; omega))

set_option maxHeartbeats 4000000 in
/-- The king comes inside on the last rank: the lone king opposes it again. -/
theorem w4_w5_u7 {c u w : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sw : Sw c u w) (hw : w ≤ 7) :
    W4 u 7 c w 5 := by
  unfold Sw at sw
  refine Or.inr ⟨u, 5, by w4s, by unfold K4; omega, by unfold Sq4; omega,
    Or.inr ⟨by unfold B4; omega, Or.inl ?_⟩⟩
  unfold Op4
  omega

set_option maxHeartbeats 4000000 in
theorem w4_w5_w7 {c u w : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sw : Sw c u w) (hw : w ≤ 7) :
    W4 w 7 c w 5 := by
  have m := m4_w7 hc sw
  unfold Sw at sw
  exact Or.inr ⟨u, 5, by w4s, by unfold K4; omega, by unfold Sq4; omega,
    Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl m)⟩⟩

set_option maxHeartbeats 4000000 in
theorem w4_w4_w6 {c u w : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sw : Sw c u w) (hw : w ≤ 7) :
    W4 w 6 c w 4 := by
  have m := m4_w6 hc sw
  unfold Sw at sw
  exact Or.inr ⟨u, 4, by w4s, by unfold K4; omega, by unfold Sq4; omega,
    Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl m)⟩⟩

set_option maxHeartbeats 4000000 in
/-- The king goes outside on the last rank: the lone king follows and opposes it. -/
theorem w4_u5_w7 {c u w : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sw : Sw c u w) (hw : w ≤ 7) :
    W4 w 7 c u 5 := by
  unfold Sw at sw
  refine Or.inr ⟨w, 5, by w4s, by unfold K4; omega, by unfold Sq4; omega,
    Or.inr ⟨by unfold B4; omega, Or.inl ?_⟩⟩
  unfold Op4
  omega

set_option maxHeartbeats 4000000 in
theorem w4_x7 {c : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) : W4 (c + 4) 7 c (c + 3) 5 :=
  Or.inr ⟨c + 2, 6, by w4s, by unfold K4; omega, by unfold Sq4; omega,
    Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl (m4_x7 hc))⟩⟩

set_option maxHeartbeats 4000000 in
theorem w4_low {x y c u w : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sw : Sw c u w) (hy : y ≤ 3)
    (side : (u = c + 2 ∧ u ≤ x) ∨ (u + 2 = c ∧ x ≤ u)) (hw : w ≤ 7) : W4 x y c w 5 := by
  have m := m4_low hc hy side
  unfold Sw at sw
  exact Or.inr ⟨u, 6, by w4s, by unfold K4; omega, by unfold Sq4; omega,
    Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl m)⟩⟩

set_option maxHeartbeats 4000000 in
/-- Two files out on the sixth rank with the king on the last rank: the lone king steps
beside the pawn and takes it next move. -/
theorem w4_u5_top {x c t o u : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sd : Sd c t o u) (hx : x ≤ 7)
    (hu : u ≤ 7) : W4 x 7 c u 5 := by
  unfold Sd at sd
  refine Or.inr ⟨t, 4, by w4s, by unfold K4; omega, by unfold Sq4; omega,
    Or.inr ⟨by unfold B4; omega, Or.inr (Or.inr (Or.inl
      ⟨by unfold Near; omega, by unfold Near; omega, ?_⟩))⟩⟩
  intro p q n1 n2
  unfold Near at n1 n2
  omega

set_option maxHeartbeats 4000000 in
/-- Next to the pawn's file on the seventh rank the lone king steps in front of the pawn. -/
theorem w4_t6_top {x c t o u : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sd : Sd c t o u) (hx : x ≤ 7)
    (ap0 : Apart x 7 t 6) : W4 x 7 c t 6 := by
  unfold Sd at sd
  unfold Apart at ap0
  exact Or.inr ⟨c, 5, by w4s, s4_center hc rfl (Or.inl rfl) (by unfold K4; omega)
    (by unfold B4; omega)⟩

set_option maxHeartbeats 4000000 in
theorem ex_t7 {a b c t o u x y : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (h : M4 a b c t 7)
    (hb : b ≤ 7) (s0 : Near a b x y) (kx : ¬ K4 x y c) (ap0 : Apart x y t 7)
    (nap : ¬ Apart x y c 6) : False := by
  obtain ⟨-, -, -, r4, -⟩ := m4_side hc sd h
  unfold Sd at sd
  have n4 := rc1_not hc (by omega) r4 (by unfold Ch; omega)
  clear r4 h
  unfold Ch at n4
  unfold Near at s0
  unfold K4 at kx
  unfold Apart at ap0 nap
  omega

set_option maxHeartbeats 4000000 in
theorem ex_u6 {a b c t o u x y : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (h : M4 a b c u 6)
    (hb : b ≤ 7) (nk : ¬ K4 a b c) (k1 : Apart a b u 6) (s0 : Near a b x y) (kx : ¬ K4 x y c)
    (ap0 : Apart x y u 6) (nap : ¬ Apart x y t 6) : False := by
  obtain ⟨-, -, -, r4, -⟩ := m4_side hc sd h
  unfold Sd at sd
  have n4 := rc1_not hc (by omega) r4 (by unfold Ch; omega)
  clear r4 h
  unfold Ch at n4
  unfold Near at s0
  unfold K4 at kx nk
  unfold Apart at ap0 nap k1
  omega

set_option maxHeartbeats 4000000 in
theorem ex_w6 {a b c t o u w x y : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (sw : Sw c u w)
    (h : M4 a b c w 6) (hb : b ≤ 7) (nk : ¬ K4 a b c) (k1 : Apart a b w 6) (s0 : Near a b x y)
    (kx : ¬ K4 x y c) (ap0 : Apart x y w 6) (nap : ¬ Apart x y u 6) : False := by
  obtain ⟨-, -, -, r4, -⟩ := m4_side hc sd h
  unfold Sd at sd
  unfold Sw at sw
  have n4 := rc1_not hc (by omega) r4 (by unfold Ch; omega)
  clear r4 h
  unfold Ch at n4
  unfold Near at s0
  unfold K4 at kx nk
  unfold Apart at ap0 nap k1
  omega

set_option maxHeartbeats 4000000 in
theorem ex_u7 {a b c t o u x y : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (h : M4 a b c u 7)
    (hb : b ≤ 7) (nk : ¬ K4 a b c) (nb : ¬ B4 a b c) (k1 : Apart a b u 7) (s0 : Near a b x y)
    (kx : ¬ K4 x y c) (ap0 : Apart x y u 7) (nap : ¬ Apart x y t 6) : False := by
  obtain ⟨r1, -, -, r4, os⟩ := m4_side hc sd h
  unfold Sd at sd
  have n1 := rc1_not hc (by omega) r1 (by unfold Ch; omega)
  have n4 := rc1_not hc (by omega) r4 (by unfold Ch; omega)
  have nu := os_not 1 os (by unfold Ch; omega)
  clear r1 r4 os h
  unfold K4 at kx nk
  unfold B4 at nb
  unfold Apart at ap0 nap k1
  have pos : (x = c ∧ y = 7) ∨ (x = u ∧ y = 5) := by omega
  unfold Near at s0
  unfold Btw at nu
  unfold Ch at n1 n4 nu
  rcases pos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · clear n1 nu nb
    omega
  · clear n4
    omega

set_option maxHeartbeats 4000000 in
theorem ex_w7 {a b c t o u w x y : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (sw : Sw c u w)
    (h : M4 a b c w 7) (hb : b ≤ 7) (nk : ¬ K4 a b c) (k1 : Apart a b w 7) (s0 : Near a b x y)
    (kx : ¬ K4 x y c) (ap0 : Apart x y w 7) (nap : ¬ Apart x y u 6) : False := by
  obtain ⟨-, -, -, r4, os⟩ := m4_side hc sd h
  unfold Sd at sd
  unfold Sw at sw
  have n4 := rc1_not hc (by omega) r4 (by unfold Ch; omega)
  have nu := os_not 2 os (by unfold Ch; omega)
  clear r4 os h
  unfold K4 at kx nk
  unfold Apart at ap0 nap k1
  have pos : (x = t ∧ y = 7) ∨ ((x = u ∨ x = w) ∧ y = 5) := by omega
  unfold Near at s0
  unfold Btw at nu
  unfold Ch at n4 nu
  rcases pos with ⟨rfl, rfl⟩ | ⟨px, rfl⟩
  · clear nu
    omega
  · clear n4
    omega

set_option maxHeartbeats 4000000 in
theorem ex_t4 {a b c t o u x y : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (h : M4 a b c t 4)
    (k1 : Apart a b t 4) (k2 : ¬ (a = c ∧ b = 4)) (s0 : Near a b x y)
    (np : ¬ (x = c ∧ y = 4)) (kx : ¬ K4 x y c) (ap0 : Apart x y t 4)
    (nap : ¬ Apart x y c 5) : False := by
  obtain ⟨-, -, r3, -, -⟩ := m4_side hc sd h
  unfold Sd at sd
  have n3 := rc1_not hc (by omega) r3 (by unfold Ch; omega)
  have nkr : ¬ KR a b c o 5 2 := by
    intro k
    have w := r3 2 k
    unfold WR Cross Hit Ch at w
    omega
  clear r3 h
  unfold K4 at kx
  unfold Apart at ap0 nap k1
  have pos : x = o ∧ y = 4 := by omega
  obtain ⟨rfl, rfl⟩ := pos
  unfold Near at s0
  unfold KR Thru Ch at nkr
  unfold Ch at n3
  omega

set_option maxHeartbeats 4000000 in
/-- Three files out on the sixth rank. -/
theorem w4_w5 {a b c t o u w x y : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sd : Sd c t o u)
    (sw : Sw c u w) (h : M4 a b c w 5) (hb : b ≤ 7) (hw : w ≤ 7) (s0 : Near a b x y)
    (kx : ¬ K4 x y c) (ap0 : Apart x y w 5) (nap : ¬ Apart x y u 6) : W4 x y c w 5 := by
  obtain ⟨-, r2, -, -, -⟩ := m4_side hc sd h
  have sd' := sd
  unfold Sd at sd'
  have sw' := sw
  unfold Sw at sw'
  have n2 := rc1_not hc (by omega) r2 (by unfold Ch; omega)
  clear r2 h
  have pos : y = 7 ∧ (x = u ∨ x = w) := by
    unfold Ch at n2
    unfold Near at s0
    unfold K4 at kx
    unfold Apart at ap0 nap
    omega
  obtain ⟨rfl, rfl | rfl⟩ := pos
  · exact w4_w5_u7 hc h3 sw hw
  · exact w4_w5_w7 hc h3 sw hw

set_option maxHeartbeats 4000000 in
/-- Three files out on the pawn's rank. -/
theorem w4_w4 {a b c t o u w x y : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sd : Sd c t o u)
    (sw : Sw c u w) (h : M4 a b c w 4) (hb : b ≤ 7) (hw : w ≤ 7) (nk : ¬ K4 a b c)
    (k1 : Apart a b w 4) (k2 : ¬ (a = c ∧ b = 4)) (s0 : Near a b x y)
    (np : ¬ (x = c ∧ y = 4)) (kx : ¬ K4 x y c) (ap0 : Apart x y w 4)
    (nap : ¬ Apart x y u 5) : W4 x y c w 4 := by
  obtain ⟨-, -, -, -, os⟩ := m4_side hc sd h
  have sd' := sd
  unfold Sd at sd'
  have sw' := sw
  unfold Sw at sw'
  have nu := os_not 2 os (by unfold Ch; omega)
  clear os h
  have pos : x = w ∧ y = 6 := by
    unfold K4 at kx nk
    unfold Apart at ap0 nap k1
    have cand : (x = t ∧ y = 4) ∨ (x = u ∧ y = 6) ∨ (x = w ∧ y = 6) := by omega
    unfold Near at s0
    unfold Btw at nu
    unfold Ch at nu
    rcases cand with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | q
    · omega
    · omega
    · exact q
  obtain ⟨rfl, rfl⟩ := pos
  exact w4_w4_w6 hc h3 sw hw

set_option maxHeartbeats 4000000 in
/-- The default reply is blocked. -/
theorem w4_blocked {a b c e f x y u' v' : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (h : M4 a b c e f) (st : KingStep a b c 4 e f x y) (nb : ¬ B4 a b c) (nk : ¬ K4 a b c)
    (sq : Sq4 c e f) (mv : ¬ (e = c ∧ f = 6)) (n24 : ¬ (f = 4 ∧ (e = c + 2 ∨ e + 2 = c)))
    (tw : Toward e f c 6 u' v') (nap : ¬ Apart x y u' v') : W4 x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  have s0 := st.1
  have np := st.k6
  have ap0 : Apart x y e f := st.2.2.2.2
  have k1 : Apart a b e f := D.1.k1
  have k2 := D.1.k2
  have k3 := D.1.k3
  have k4 := D.k4
  have kx : ¬ K4 x y c := k4_step hc h nb nk s0 ap0 k1 k2
  unfold Sq4 at sq
  unfold Toward at tw
  have row : f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 := by omega
  by_cases mid : e = c
  · subst mid
    have tu : u' = e ∧ v' = 6 := by omega
    rw [tu.1, tu.2] at nap
    unfold K4 at kx
    unfold Apart at nap ap0
    rcases row with rfl | rfl | rfl | rfl
    · omega
    · exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
    · omega
    · omega
  obtain ⟨t, o, u, sd, ev⟩ := side_exists hc mid sq.1 sq.2.1
  have sd' := sd
  unfold Sd at sd'
  rcases ev with rfl | rfl | sw
  · rcases row with rfl | rfl | rfl | rfl
    · have tu : u' = c ∧ v' = 5 := by omega
      rw [tu.1, tu.2] at nap
      exact (ex_t4 hc sd h k1 k2 s0 np kx ap0 nap).elim
    · omega
    · have tu : u' = c ∧ v' = 6 := by omega
      rw [tu.1, tu.2] at nap
      have y7 : y = 7 := by
        unfold K4 at kx
        unfold Apart at nap
        omega
      subst y7
      exact w4_t6_top hc u3 sd n5 ap0
    · have tu : u' = c ∧ v' = 6 := by omega
      rw [tu.1, tu.2] at nap
      exact (ex_t7 hc sd h u2 s0 kx ap0 nap).elim
  · have tu : u' = t ∧ v' = 6 := by omega
    rw [tu.1, tu.2] at nap
    rcases row with rfl | rfl | rfl | rfl
    · omega
    · have y7 : y = 7 := by
        unfold K4 at kx
        unfold Apart at nap ap0
        omega
      subst y7
      exact w4_u5_top hc u3 sd n5 u6
    · exact (ex_u6 hc sd h u2 nk k1 s0 kx ap0 nap).elim
    · exact (ex_u7 hc sd h u2 nk nb k1 s0 kx ap0 nap).elim
  · have sw' := sw
    unfold Sw at sw'
    rcases row with rfl | rfl | rfl | rfl
    · have tu : u' = u ∧ v' = 5 := by omega
      rw [tu.1, tu.2] at nap
      exact w4_w4 hc u3 sd sw h u2 u6 nk k1 k2 s0 np kx ap0 nap
    · have tu : u' = u ∧ v' = 6 := by omega
      rw [tu.1, tu.2] at nap
      exact w4_w5 hc u3 sd sw h u2 u6 s0 kx ap0 nap
    · have tu : u' = u ∧ v' = 6 := by omega
      rw [tu.1, tu.2] at nap
      exact (ex_w6 hc sd sw h u2 nk k1 s0 kx ap0 nap).elim
    · have tu : u' = u ∧ v' = 6 := by omega
      rw [tu.1, tu.2] at nap
      exact (ex_w7 hc sd sw h u2 nk k1 s0 kx ap0 nap).elim

set_option maxHeartbeats 4000000 in
/-- Opposed kings on an outer file: every king move has its answer. -/
theorem w4_op {a b c e f x y : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (op : Op4 a b c e f)
    (sq : Sq4 c e f) (st : KingStep a b c 4 e f x y) : W4 x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  have ap0 : Apart x y e f := st.2.2.2.2
  have k5 := st.k5
  unfold Op4 at op
  unfold Sq4 at sq
  obtain ⟨he, rfl, q⟩ := op
  have mid : e ≠ c := by omega
  obtain ⟨t, o, u, sd, ev⟩ := side_exists hc mid sq.1 sq.2.1
  have sd' := sd
  unfold Sd at sd'
  unfold Apart at ap0
  rcases ev with rfl | rfl | sw
  · omega
  · have y7 : y = 7 := by omega
    subst y7
    by_cases g : x = t
    · subst g
      exact w4_u5_top hc u3 sd n5 u6
    · have sw : Sw c e x := by unfold Sw; omega
      exact w4_u5_w7 hc u3 sw n5
  · have sw' := sw
    unfold Sw at sw'
    by_cases top : b = 7
    · have y7 : y = 7 := by omega
      subst y7
      by_cases g : x = u
      · subst g
        exact w4_w5_u7 hc u3 sw u6
      · have pos : e = c + 3 ∧ x = c + 4 := by omega
        obtain ⟨rfl, rfl⟩ := pos
        exact w4_x7 hc u3
    · exact w4_low hc u3 sw (by omega) (by omega) u6

set_option maxHeartbeats 4000000 in
/-- Every king move inside the fifth-rank region has its answer. -/
theorem s4_king {a b c e f x y : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (h : S4 a b c e f)
    (st : KingStep a b c 4 e f x y) : W4 x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  have s0 := st.1
  have np := st.k6
  have ap0 : Apart x y e f := st.2.2.2.2
  have k1 : Apart a b e f := D.1.k1
  have k2 := D.1.k2
  obtain ⟨nk, sq, rest⟩ := h
  rcases rest with ⟨bes, rfl, ee⟩ | ⟨nb, rest⟩
  · unfold B4 at bes
    obtain ⟨rfl, side⟩ := bes
    rcases ee with he | he
    · exact w4_bes hc u3 n5 n6 side he s0 ap0 np
    · subst he
      exact w4_c6 hc u3 n5 n6 ap0 np
  rcases rest with op | m | pr | rr
  · exact w4_op D hc op sq st
  · by_cases c6 : e = c ∧ f = 6
    · obtain ⟨rfl, rfl⟩ := c6
      exact w4_c6 hc u3 n5 n6 ap0 np
    by_cases u4' : f = 4 ∧ (e = c + 2 ∨ e + 2 = c)
    · obtain ⟨rfl, side⟩ := u4'
      have kx : ¬ K4 x y c := k4_step hc m nb nk s0 ap0 k1 k2
      rcases side with rfl | hl
      · have sd : Sd c (c + 1) (c - 1) (c + 2) := Or.inl ⟨rfl, by omega, rfl⟩
        exact w4_u4 D hc sd m.1.2.2.1 m.1.2.2.2 nk nb st
          (fun near => m4_u4r hc m s0 np kx near ap0)
      · have e2 : e = c - 2 := by omega
        subst e2
        have sd : Sd c (c - 1) (c + 1) (c - 2) := Or.inr ⟨by omega, rfl, by omega⟩
        exact w4_u4 D hc sd m.1.1 m.1.2.1 nk nb st
          (fun near => m4_u4l hc m s0 np kx near ap0)
    obtain ⟨u', v', tw⟩ := toward_exists e f c
    by_cases fr : Apart x y u' v'
    · refine w4_main D hc m st nb nk sq c6 u4' (fun u v t2 => ?_)
      obtain ⟨rfl, rfl⟩ := toward_unique tw t2
      exact fr
    · exact w4_blocked D hc m st nb nk sq c6 u4' tw fr
  · exact w4_take pr s0 ap0
  · unfold Rr4 at rr
    obtain ⟨r1, rfl, r3⟩ := rr
    have e2 : e = c - 2 := by omega
    subst e2
    exact w4_far hc u3 n5 n6 r3 s0

/-- Pawn on the fifth, sixth or seventh rank. -/
def fiveGuard : Guard where
  S a b c d e f := sixGuard.S a b c d e f ∨ (d = 4 ∧ 2 ≤ c ∧ S4 a b c e f)
  W a b c d e f := sixGuard.W a b c d e f ∨ (d = 4 ∧ 2 ≤ c ∧ W4 a b c e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | ⟨rfl, hc, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := sixGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r),
        fun p r t => Or.inl (q3 p r t), q4⟩
    · exact ⟨fun x y st => Or.inr ⟨rfl, hc, s4_king D hc h st⟩,
        fun fr _ => Or.inl (Or.inr ⟨rfl, hc, s4_push D hc h fr⟩),
        fun q => by omega, fun q => by omega⟩
  weak := by
    intro a b c d e f D h
    rcases h with h | ⟨rfl, hc, h⟩
    · rcases sixGuard.weak D h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inl q⟩)
    · rcases h with q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr ⟨rfl, hc, q⟩⟩)

open EndgameChess.KK in
/-- Bishop or centre pawn on the fifth, sixth or seventh rank, a fresh root in the guard
with the pawn owner to move: the lone king holds. -/
theorem fresh_five_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (sat : SD fiveGuard σ sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong h fresh turn safe sat

end EndgameChess.Rules.KPK.Coord
