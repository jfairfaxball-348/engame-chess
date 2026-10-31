import EndgameChess.Rules.KPK.Coord.Five

/-! Fifth-rank guard: the lone king two files out on the pawn's rank. -/
namespace EndgameChess.Rules.KPK.Coord

set_option maxHeartbeats 4000000 in
/-- What the race says about a lone king two files out: the king is far from the far side. -/
theorem u4_far {a b c t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (r5 : Rc a b c u 4 o 5)
    (r6 : Rc a b c u 4 o 6) : ¬ KR a b c o 5 3 ∧ ¬ Ch a b o 6 3 := by
  unfold Sd at sd
  constructor
  · intro k
    have w := r5 3 k
    unfold WR Cross Hit Ch at w
    omega
  · intro k
    have w := r6 3 ⟨k, Or.inl (by unfold Thru; omega)⟩
    unfold WR Cross Hit Ch at w
    omega

set_option maxHeartbeats 4000000 in
theorem w4_u4 {a b c t o u x y : Nat} (D : DomS a b c 4 u 4) (hc : 2 ≤ c) (sd : Sd c t o u)
    (r5 : Rc a b c u 4 o 5) (r6 : Rc a b c u 4 o 6) (nk : ¬ K4 a b c) (nb : ¬ B4 a b c)
    (st : KingStep a b c 4 u 4 x y) (mk : ¬ Ch x y t 6 1 → M4 x y c t 4) : W4 x y c u 4 := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  have ⟨f5, f6⟩ := u4_far hc sd r5 r6
  have sd' := sd
  unfold Sd at sd'
  have s0 := st.1
  have np := st.k6
  have ap0 : Apart x y u 4 := st.2.2.2.2
  unfold KR Thru Ch at f5
  unfold Ch at f6
  unfold Apart at ap0
  unfold K4 at nk
  unfold B4 at nb
  have ap : Apart x y t 4 := by
    unfold Apart
    rcases sd' with q | q <;> omega
  have kx : ¬ K4 x y c := by
    unfold K4
    rcases sd' with q | q <;> omega
  have bx : ¬ B4 x y c := by
    unfold B4
    rcases sd' with q | q <;> omega
  have step : WeakStep x y c 4 u 4 t 4 := by
    unfold Apart at ap
    unfold WeakStep Near Apart Att
    omega
  have sq : Sq4 c t 4 := by unfold Sq4; omega
  by_cases near : Ch x y t 6 1
  · refine Or.inr ⟨t, 4, step, kx, sq, Or.inr ⟨bx, Or.inr (Or.inr (Or.inl ?_))⟩⟩
    unfold Ch at near
    unfold K4 at kx
    refine ⟨by unfold Near; omega, by unfold Near; omega, ?_⟩
    intro p q m1 m2
    unfold Near at m1 m2
    unfold Apart
    rcases sd' with g | g <;> omega
  · exact Or.inr ⟨t, 4, step, kx, sq, Or.inr ⟨bx, Or.inr (Or.inl (mk near))⟩⟩

set_option maxHeartbeats 4000000 in
theorem oc_side {a b c x y g t t' : Nat} (h : Oc a b c g 4 t) (hg : g = c + 2 ∨ g + 2 = c) (hc : 2 ≤ c)
    (s : Near a b x y) (st : t' = c + 1 ∨ t' + 1 = c) (no : ¬ Ch x y t 5 0 ∧ ¬ Ch x y t 6 0) :
    Oc x y c t' 4 t := by
  intro n kr
  have zero : n ≠ 0 := by
    intro z
    subst z
    rcases kr with kr | kr
    · exact no.1 kr
    · exact no.2 kr
  left
  unfold Ch
  omega

/-- The main race after the step beside the pawn, right side. -/
theorem m4_u4r {a b c x y : Nat} (hc : 2 ≤ c) (h : M4 a b c (c + 2) 4) (s : Near a b x y)
    (np : ¬ (x = c ∧ y = 4)) (kx : ¬ K4 x y c) (near : ¬ Ch x y (c + 1) 6 1) (ap : Apart x y (c + 2) 4) :
    M4 x y c (c + 1) 4 := by
  have sd : Sd c (c + 1) (c - 1) (c + 2) := Or.inl ⟨rfl, by omega, rfl⟩
  obtain ⟨⟨-, -, r3, r4⟩, o1, o2⟩ := h
  refine ⟨⟨rc_t5 sd ?_, rc_t6 sd near, rc_o hc sd (Or.inl rfl) r3 s np, rc_o hc sd (Or.inr rfl) r4 s np⟩, ?_, ?_⟩
  · unfold Ch K4 at *
    omega
  · rcases o1 with ⟨h1, h2, -⟩ | o1
    · left
      unfold Near at s
      omega
    · right
      refine oc_side o1 (Or.inl rfl) hc s (Or.inl rfl) ⟨?_, ?_⟩
      · unfold Ch; unfold Apart at ap; omega
      · unfold Ch at *; omega
  · rcases o2 with ⟨h1, -⟩ | o2
    · omega
    · right
      intro n kr
      have old := o2 (n + 1) (by
        rcases kr with g | g
        · exact Or.inl (ch_step s g)
        · exact Or.inr (ch_step s g))
      left
      unfold Ch at *
      omega

/-- The same on the left. -/
theorem m4_u4l {a b c x y : Nat} (hc : 2 ≤ c) (h : M4 a b c (c - 2) 4) (s : Near a b x y)
    (np : ¬ (x = c ∧ y = 4)) (kx : ¬ K4 x y c) (near : ¬ Ch x y (c - 1) 6 1) (ap : Apart x y (c - 2) 4) :
    M4 x y c (c - 1) 4 := by
  have sd : Sd c (c - 1) (c + 1) (c - 2) := Or.inr ⟨by omega, rfl, by omega⟩
  obtain ⟨⟨r1, r2, -, -⟩, o1, o2⟩ := h
  refine ⟨⟨rc_o hc sd (Or.inl rfl) r1 s np, rc_o hc sd (Or.inr rfl) r2 s np, rc_t5 sd ?_, rc_t6 sd near⟩, ?_, ?_⟩
  · unfold Ch K4 at *
    omega
  · rcases o1 with ⟨h1, -⟩ | o1
    · omega
    · right
      intro n kr
      have old := o1 (n + 1) (by
        rcases kr with g | g
        · exact Or.inl (ch_step s g)
        · exact Or.inr (ch_step s g))
      left
      unfold Ch at *
      omega
  · rcases o2 with ⟨h1, h2, -⟩ | o2
    · left
      unfold Near at s
      omega
    · right
      refine oc_side o2 (Or.inr (by omega)) hc s (Or.inr (by omega)) ⟨?_, ?_⟩
      · unfold Ch; unfold Apart at ap; omega
      · unfold Ch at *; omega

end EndgameChess.Rules.KPK.Coord
