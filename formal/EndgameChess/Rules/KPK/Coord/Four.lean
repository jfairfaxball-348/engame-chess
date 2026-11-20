import EndgameChess.Rules.KPK.Coord.KnFive

/-! Fourth-rank draws, pawn owner to move. The region is the fifth-rank region `S4` with
both kings and the pawn one rank higher: below the edge, the geometry of kings and pawn
does not change when everything moves up a rank. The lone king must not stand on the last
rank, and a king on the last rank stays there when lifted. A king step then lifts to a king
step one rank up, except a step between the last two ranks, which lifts to no move. -/
namespace EndgameChess.Rules.KPK.Coord

/-- The strong king's rank one higher, held on the last rank. -/
def Lift (b B : Nat) : Prop := (b ≤ 6 ∧ B = b + 1) ∨ (b = 7 ∧ B = 7)

/-- The fourth-rank draw region: the fifth-rank region one rank up. -/
def S3 (a b c e f : Nat) : Prop :=
  f ≤ 6 ∧ ∃ B, Lift b B ∧ Apart a B e (f + 1) ∧ S4 a B c e (f + 1)

/-- The lone king's answer at height 3. -/
def W3 (a b c e f : Nat) : Prop :=
  Capture a b c 3 e f ∨ ∃ x y, WeakStep a b c 3 e f x y ∧ S3 a b c x y

theorem lift_exists {b : Nat} (hb : b ≤ 7) : ∃ B, Lift b B := by
  by_cases g : b ≤ 6
  · exact ⟨b + 1, Or.inl ⟨g, rfl⟩⟩
  · exact ⟨7, Or.inr ⟨by omega, rfl⟩⟩

theorem lift_unique {b B B' : Nat} (h : Lift b B) (h' : Lift b B') : B = B' := by
  unfold Lift at h h'
  omega

set_option maxHeartbeats 4000000 in
/-- An answer one rank up is an answer here. -/
theorem w3_of_w4 {x y Y c e f : Nat} (hl : Lift y Y) (h : W4 x Y c e (f + 1)) :
    W3 x y c e f := by
  unfold Lift at hl
  rcases h with ⟨n1, n2⟩ | ⟨u, v, st, s⟩
  · left
    unfold Capture Near at *
    omega
  · have v4 : 4 ≤ v := s.2.1.2.2
    have ap : Apart x Y u v := st.2.2.2.2.1
    have v7 : v ≤ 7 := st.2.2.1
    refine Or.inr ⟨u, v - 1, ?_, by omega, Y, Or.imp id id hl, ?_, ?_⟩
    · unfold WeakStep Near Apart Att at st ⊢
      omega
    · rw [show v - 1 + 1 = v by omega]
      exact ap
    · rw [show v - 1 + 1 = v by omega]
      exact s

set_option maxHeartbeats 4000000 in
/-- A fourth-rank position lifts to an admissible fifth-rank position. -/
theorem dom_lift {a b B c e f : Nat} (D : DomS a b c 3 e f) (hl : Lift b B) (hf : f ≤ 6)
    (ap : Apart a B e (f + 1)) : DomS a B c 4 e (f + 1) := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k2 := D.1.k2
  have k3 := D.1.k3
  have k4 := D.k4
  unfold Lift at hl
  refine ⟨⟨by omega, by omega, u3, by omega, by omega, u6, by omega, by omega, by omega, ap⟩, ?_⟩
  unfold Att
  omega

set_option maxHeartbeats 4000000 in
/-- A king step that changes the lifted square lifts to a king step. -/
theorem step_lift {a b B c e f x y Y : Nat} (hl : Lift b B) (hl' : Lift y Y)
    (st : KingStep a b c 3 e f x y) (ne : ¬ (a = x ∧ B = Y)) (apY : Apart x Y e (f + 1)) :
    KingStep a B c 4 e (f + 1) x Y := by
  unfold Lift at hl hl'
  refine ⟨?_, st.2.1, by omega, ?_, apY⟩
  · unfold KingStep Near at st
    unfold Near
    omega
  · have := st.k6
    omega

/-- The region is closed under king steps that change the lifted square. -/
theorem s3_king_moved {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : S3 a b c e f) (st : KingStep a b c 3 e f x y)
    (moved : ∀ B Y, Lift b B → Lift y Y → ¬ (a = x ∧ B = Y) ∧ Apart x Y e (f + 1)) :
    W3 x y c e f := by
  obtain ⟨hf, B, hl, ap, s⟩ := h
  obtain ⟨Y, hl'⟩ := lift_exists st.2.2.1
  obtain ⟨ne, apY⟩ := moved B Y hl hl'
  exact w3_of_w4 hl' (s4_king (dom_lift D hl hf ap) hc s (step_lift hl hl' st ne apY))

/-! ## The pass at the last rank

Lifted, a strong king step between the last two ranks is no move at all. The lone king
then still has an answer: with the king on the last rank its races only get shorter. -/

theorem kr_mono {a b c p q n : Nat} (h : KR a b c p q n) : KR a b c p q (n + 1) := by
  unfold KR Ch at *
  omega

/-- A race survives the lone king's step when the king stays put. -/
theorem rc_pass {a b c e f u v p q : Nat} (hc : 1 ≤ c) (hp : p = c + 1 ∨ p + 1 = c)
    (hq : q = 5 ∨ q = 6) (h : Rc a b c e f p q) (far : ¬ Ch a b p q 0)
    (t : Toward e f c 6 u v) (safe : ¬ (v = 5 ∧ (u = c + 1 ∨ u + 1 = c))) : Rc a b c u v p q := by
  intro n kr
  have old := h (n + 1) (kr_mono kr)
  by_cases zero : n = 0
  · subst zero
    exact absurd kr.1 far
  · exact wr_step hc hp hq (by omega) t safe old

theorem oc_pass {a b c e f u v t : Nat} (h : Oc a b c e f t) (st : Toward e f c 6 u v)
    (mv : ¬ (e = c ∧ f = 6)) : Oc a b c u v t := by
  intro n kr
  have old := h (n + 1) (by
    unfold Ch at kr ⊢
    omega)
  unfold Ch at *
  unfold Toward at st
  omega

theorem ocr_pass {a b c e f u v : Nat} (h : Ocr a b c e f) (st : Toward e f c 6 u v)
    (mv : ¬ (e = c ∧ f = 6)) (hf : 4 ≤ f ∧ f ≤ 7) : Ocr a b c u v := by
  rcases h with ⟨h1, h2, h3⟩ | h
  · by_cases g : c < u
    · left
      unfold Toward at st
      omega
    · right
      intro n _
      unfold Toward at st
      unfold Ch
      omega
  · exact Or.inr (oc_pass h st mv)

theorem ocl_pass {a b c e f u v : Nat} (h : Ocl a b c e f) (st : Toward e f c 6 u v)
    (mv : ¬ (e = c ∧ f = 6)) (hf : 4 ≤ f ∧ f ≤ 7) : Ocl a b c u v := by
  rcases h with ⟨h1, h2, h3⟩ | h
  · by_cases g : u < c
    · left
      unfold Toward at st
      omega
    · right
      intro n _
      unfold Toward at st
      unfold Ch
      omega
  · exact Or.inr (oc_pass h st mv)

/-- Every race survives the lone king's step towards the pawn when the king stays on the
last rank. -/
theorem m4_pass {a c e f u v : Nat} (hc : 1 ≤ c) (h : M4 a 7 c e f) (st : Toward e f c 6 u v)
    (safe : ¬ (v = 5 ∧ (u = c + 1 ∨ u + 1 = c))) (mv : ¬ (e = c ∧ f = 6)) (hf : 4 ≤ f ∧ f ≤ 7) :
    M4 a 7 c u v := by
  obtain ⟨⟨r1, r2, r3, r4⟩, o1, o2⟩ := h
  have far (p q : Nat) (hq : q = 5 ∨ q = 6) : ¬ Ch a 7 p q 0 := by
    unfold Ch
    omega
  exact ⟨⟨rc_pass hc (Or.inl rfl) (Or.inl rfl) r1 (far _ _ (Or.inl rfl)) st safe,
    rc_pass hc (Or.inl rfl) (Or.inr rfl) r2 (far _ _ (Or.inr rfl)) st safe,
    rc_pass hc (Or.inr (by omega)) (Or.inl rfl) r3 (far _ _ (Or.inl rfl)) st safe,
    rc_pass hc (Or.inr (by omega)) (Or.inr rfl) r4 (far _ _ (Or.inr rfl)) st safe⟩,
    ocr_pass o1 st mv hf, ocl_pass o2 st mv hf⟩

set_option maxHeartbeats 4000000 in
/-- Beside the pawn, with the king on the last rank, the lone king takes the pawn next. -/
theorem s4_beside7 {a c u : Nat} (hc : 1 ≤ c) (side : u = c + 1 ∨ u + 1 = c) :
    S4 a 7 c u 4 := by
  refine ⟨by unfold K4; omega, by unfold Sq4; omega, Or.inr ⟨by unfold B4; omega,
    Or.inr (Or.inr (Or.inl ⟨by unfold Near; omega, by unfold Near; omega, ?_⟩))⟩⟩
  intro x y n1 n2
  unfold Near at n1 n2
  omega

set_option maxHeartbeats 4000000 in
theorem w4_beside7 {a c e f u : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a ≤ 7) (side : u = c + 1 ∨ u + 1 = c)
    (s : Near e f u 4) (hf : f ≤ 5) (ne : ¬ (e = c ∧ f = 4)) : W4 a 7 c e f := by
  refine Or.inr ⟨u, 4, ?_, s4_beside7 hc side⟩
  unfold WeakStep Near Apart Att at *
  omega

set_option maxHeartbeats 4000000 in
/-- The main race with the king on the last rank and no king move: the lone king steps
towards the square two ahead of the pawn. -/
theorem w4_pass_main {a c e f : Nat} (D : DomS a 7 c 4 e f) (hc : 1 ≤ c) (h : M4 a 7 c e f)
    (sq : Sq4 c e f) (mv : ¬ (e = c ∧ f = 6)) (n24 : ¬ (f = 4 ∧ (e = c + 2 ∨ e + 2 = c)))
    (nop : ¬ Op4 a 7 c e f) (nt : ¬ Near e f c 4) : W4 a 7 c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨u, v, tw⟩ := toward_exists e f c
  have k1 : Apart a 7 e f := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  have m := id h
  obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := m
  have a1 := rc1 hc (Or.inl rfl) r2
  have a2 := rc1 hc (Or.inr (by omega)) r4
  have a3 := rc2 hc (Or.inl rfl) r2
  have a4 := rc2 hc (Or.inr (by omega)) r4
  have a5 := rc1 hc (Or.inl rfl) r1
  have a6 := rc1 hc (Or.inr (by omega)) r3
  clear r1 r2 r3 r4
  unfold Sq4 at sq
  have tw' := tw
  unfold Toward at tw'
  have safe : ¬ (v = 5 ∧ (u = c + 1 ∨ u + 1 = c)) := by omega
  have new := m4_pass hc h tw safe mv ⟨sq.2.2, u7⟩
  have ap : Apart a 7 u v := by
    have b3 : ¬ Ch a 7 (c + 1) 6 2 ∨ Ch e f (c + 1) 6 2 := a3.imp id (fun w => w.1)
    have b4 : ¬ Ch a 7 (c - 1) 6 2 ∨ Ch e f (c - 1) 6 2 := a4.imp id (fun w => w.1)
    clear new h a3 a4
    refine Classical.byContradiction fun hb => ?_
    have hv : v = 6 ∧ u ≤ a + 1 ∧ a ≤ u + 1 := by
      unfold Apart at hb
      omega
    clear hb tw
    unfold Ch at a1 a2 a5 a6 b3 b4
    unfold Op4 at nop
    unfold Near at nt
    unfold Apart at k1
    omega
  refine Or.inr ⟨u, v, ⟨?_, by omega, by omega, ?_, ap, ?_⟩, by unfold K4; omega,
    by unfold Sq4; omega, Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl new)⟩⟩
  · unfold Near; omega
  · omega
  · unfold Att; omega

set_option maxHeartbeats 4000000 in
/-- With the king on the last rank the lone king can always pass on its turn too. -/
theorem s4_pass {a c e f : Nat} (D : DomS a 7 c 4 e f) (hc : 1 ≤ c) (h : S4 a 7 c e f) :
    W4 a 7 c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 : Apart a 7 e f := D.1.k1
  have k3 := D.1.k3
  obtain ⟨nk, sq, rest⟩ := h
  have sq' := sq
  unfold Sq4 at sq'
  rcases rest with ⟨bes, -, -⟩ | ⟨nb, rest⟩
  · unfold B4 at bes
    omega
  by_cases nt : Near e f c 4
  · exact Or.inl ⟨nt, by unfold Near; omega⟩
  have opcase : Op4 a 7 c e f → W4 a 7 c e f := by
    intro op
    unfold Op4 at op
    obtain ⟨rfl, rfl, q⟩ := op
    by_cases g1 : e = c + 2
    · exact w4_beside7 hc u3 u1 (Or.inl rfl) (by unfold Near; omega) (by omega) (by omega)
    by_cases g2 : e + 2 = c
    · exact w4_beside7 hc u3 u1 (Or.inr (by omega)) (by unfold Near; omega) (by omega) (by omega)
    have sw : Sw c (if c < e then c + 2 else c - 2) e := by
      unfold Sw
      split <;> omega
    refine Or.inr ⟨if c < e then c + 2 else c - 2, 5, ?_, ?_⟩
    · unfold WeakStep Near Apart Att
      split <;> omega
    · have m := m4_w7 hc sw
      refine ⟨by unfold K4; omega, ?_, Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl m)⟩⟩
      unfold Sq4
      split <;> omega
  by_cases op : Op4 a 7 c e f
  · exact opcase op
  rcases rest with op' | m | pr | rr
  · exact absurd op' op
  · by_cases c6 : e = c ∧ f = 6
    · obtain ⟨rfl, rfl⟩ := c6
      exact w4_c6 hc u3 u1 (by omega) k1 (by omega)
    by_cases f4 : f = 4 ∧ (e = c + 2 ∨ e + 2 = c)
    · obtain ⟨rfl, side⟩ := f4
      rcases side with rfl | hl
      · exact w4_beside7 hc u3 u1 (Or.inl rfl) (by unfold Near; omega) (by omega) (by omega)
      · exact w4_beside7 hc u3 u1 (Or.inr (show c - 1 + 1 = c by omega)) (by unfold Near; omega)
          (by omega) (by omega)
    exact w4_pass_main D hc m sq c6 f4 op nt
  · obtain ⟨n1, n2, -⟩ := pr
    exact Or.inl ⟨n1, n2⟩
  · unfold Rr4 at rr
    obtain ⟨r1, rfl, -⟩ := rr
    exact w4_beside7 hc u3 u1 (Or.inr (show c - 1 + 1 = c by omega)) (by unfold Near; omega)
      (by omega) (by omega)

/-! ## A step onto the last rank beside the lone king

Lifted, the king's step onto the last rank next to a lone king on the sixth rank would
touch it. Here the lone king answers by stepping in front of the pawn or one file towards
it. -/

set_option maxHeartbeats 4000000 in
theorem m4_y7 {c : Nat} (hc : 1 ≤ c) : M4 (c + 3) 7 c (c + 1) 6 := by m4c

set_option maxHeartbeats 4000000 in
theorem m4_y7l {c x : Nat} (hx : x + 3 = c) : M4 x 7 c (c - 1) 6 := by
  have hc : 1 ≤ c := by omega
  m4c

set_option maxHeartbeats 4000000 in
/-- The races force the king three or four files out, on the far side of the lone king. -/
theorem e2_cases {a c e x : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (h : M4 a 7 c e 6) (sq : Sq4 c e 6)
    (k1 : Apart a 7 e 6) (s : a ≤ x + 1 ∧ x ≤ a + 1) (adj : x ≤ e + 1 ∧ e ≤ x + 1) :
    e = c ∨ (e = c + 1 ∧ x = c + 2) ∨ (e + 1 = c ∧ x + 2 = c) ∨ (e = c + 2 ∧ x = c + 3) ∨
      (e + 2 = c ∧ x + 3 = c) ∨ (e = c + 3 ∧ x = c + 4) := by
  obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := h
  have a1 := rc1 hc (Or.inl rfl) r2
  have a2 := rc1 hc (Or.inr (by omega)) r4
  have a3 := rc2 hc (Or.inl rfl) r2
  have a4 := rc2 hc (Or.inr (by omega)) r4
  have b3 : ¬ Ch a 7 (c + 1) 6 2 ∨ Ch e 6 (c + 1) 6 2 := a3.imp id (fun w => w.1)
  have b4 : ¬ Ch a 7 (c - 1) 6 2 ∨ Ch e 6 (c - 1) 6 2 := a4.imp id (fun w => w.1)
  clear r1 r2 r3 r4 a3 a4
  unfold Ch at a1 a2 b3 b4
  unfold Sq4 at sq
  unfold Apart at k1
  omega

theorem s3_top {x c u : Nat} (hx : x ≤ 7) (hu : u ≤ 6) (ap : Apart x 7 u 6)
    (s : S4 x 7 c u 6) : S3 x 7 c u 5 :=
  ⟨by omega, 7, Or.inr ⟨rfl, rfl⟩, ap, s⟩

set_option maxHeartbeats 4000000 in
theorem e2_reply {a c e x : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (hx : x ≤ 7) (h : M4 a 7 c e 6)
    (sq : Sq4 c e 6) (k1 : Apart a 7 e 6) (s : a ≤ x + 1 ∧ x ≤ a + 1)
    (adj : x ≤ e + 1 ∧ e ≤ x + 1) : W3 x 7 c e 5 := by
  have cs := e2_cases hc h3 h sq k1 s adj
  have kx : ¬ K4 x 7 c := by unfold K4; omega
  have bx : ¬ B4 x 7 c := by unfold B4; omega
  rcases cs with rfl | ⟨rfl, rfl⟩ | ⟨he, hx2⟩ | ⟨rfl, rfl⟩ | ⟨he, hx3⟩ | ⟨rfl, rfl⟩
  · refine Or.inr ⟨e, 4, by ws, by omega, 7, Or.inr ⟨rfl, rfl⟩, by unfold Apart; omega,
      s4_center hc rfl (Or.inl rfl) kx bx⟩
  · exact Or.inr ⟨c, 5, by ws, s3_top hx (by omega) (by unfold Apart; omega)
      (s4_center hc rfl (Or.inr rfl) kx bx)⟩
  · exact Or.inr ⟨c, 5, by ws, s3_top hx (by omega) (by unfold Apart; omega)
      (s4_center hc rfl (Or.inr rfl) kx bx)⟩
  · exact Or.inr ⟨c + 1, 5, by ws, s3_top hx (by omega) (by unfold Apart; omega)
      ⟨kx, by unfold Sq4; omega, Or.inr ⟨bx, Or.inr (Or.inl (m4_y7 hc))⟩⟩⟩
  · exact Or.inr ⟨c - 1, 5, by ws, s3_top hx (by omega) (by unfold Apart; omega)
      ⟨kx, by unfold Sq4; omega, Or.inr ⟨bx, Or.inr (Or.inl (m4_y7l hx3))⟩⟩⟩
  · exact Or.inr ⟨c + 2, 5, by ws, s3_top hx (by omega) (by unfold Apart; omega)
      ⟨kx, by unfold Sq4; omega, Or.inr ⟨bx, Or.inr (Or.inl (m4_x7 hc))⟩⟩⟩

/-- With the king on the last rank and the lone king on the sixth, the region's race is the
main race. -/
theorem s4_top_m4 {a c e : Nat} (h : S4 a 7 c e 6) : M4 a 7 c e 6 := by
  obtain ⟨-, -, rest⟩ := h
  rcases rest with ⟨bes, -, -⟩ | ⟨-, op | m | pr | rr⟩
  · unfold B4 at bes; omega
  · unfold Op4 at op; omega
  · exact m
  · obtain ⟨n1, -, -⟩ := pr
    unfold Near at n1; omega
  · unfold Rr4 at rr; omega

set_option maxHeartbeats 4000000 in
/-- The fourth-rank region is closed under every king step. -/
theorem s3_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : S3 a b c e f)
    (st : KingStep a b c 3 e f x y) : W3 x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  have h' := h
  obtain ⟨hf, B, hl, ap, s⟩ := h'
  obtain ⟨Y, hl'⟩ := lift_exists n6
  have ap0 : Apart x y e f := st.2.2.2.2
  have ne0 := st.k5
  by_cases same : a = x ∧ B = Y
  · obtain ⟨rfl, rfl⟩ := same
    have b7 : B = 7 := by
      unfold Lift at hl hl'
      omega
    subst b7
    exact w3_of_w4 hl' (s4_pass (dom_lift D hl hf ap) hc s)
  by_cases apY : Apart x Y e (f + 1)
  · refine s3_king_moved D hc h st (fun B' Y' l1 l2 => ?_)
    rw [← lift_unique hl l1, ← lift_unique hl' l2]
    exact ⟨same, apY⟩
  · have top : y = 7 ∧ Y = 7 ∧ f = 5 ∧ B = 7 ∧ x ≤ e + 1 ∧ e ≤ x + 1 := by
      unfold Lift at hl hl'
      unfold Apart at apY ap0
      omega
    obtain ⟨rfl, rfl, rfl, rfl, adj⟩ := top
    exact e2_reply hc u3 n5 (s4_top_m4 s) s.2.1 ap ⟨n1, n2⟩ adj

/-! ## The push

After the push the lone king steps straight up after the pawn, or takes it. With the king
on the last rank the lifted region is then the fifth-rank region itself. With the king
below the sixth rank, lowering it by a rank only lengthens each of its races. -/

theorem kr_up {a b c p q n : Nat} (hb : b ≤ 4) (hq : q = 5 ∨ q = 6) (h : KR a b c p q n) :
    KR a (b + 1) c p q n := by
  unfold KR Ch Thru at *
  omega

theorem rc_down {a b c e f p q : Nat} (hb : b ≤ 4) (hq : q = 5 ∨ q = 6)
    (h : Rc a (b + 1) c e f p q) : Rc a b c e f p q :=
  fun n kr => h n (kr_up hb hq kr)

theorem oc_down {a b c e f t : Nat} (hb : b ≤ 4) (h : Oc a (b + 1) c e f t) : Oc a b c e f t := by
  intro n kr
  apply h n
  unfold Ch at *
  omega

theorem m4_down {a b c e f : Nat} (hb : b ≤ 4) (h : M4 a (b + 1) c e f) : M4 a b c e f := by
  obtain ⟨⟨r1, r2, r3, r4⟩, o1, o2⟩ := h
  refine ⟨⟨rc_down hb (Or.inl rfl) r1, rc_down hb (Or.inr rfl) r2, rc_down hb (Or.inl rfl) r3,
    rc_down hb (Or.inr rfl) r4⟩, ?_, ?_⟩
  · rcases o1 with q | q
    · exact Or.inl (by omega)
    · exact Or.inr (oc_down hb q)
  · rcases o2 with q | q
    · exact Or.inl (by omega)
    · exact Or.inr (oc_down hb q)

set_option maxHeartbeats 4000000 in
/-- King diagonally behind the pawn, lone king beside the square two ahead. -/
theorem m4_b3 {c x : Nat} (hc : 1 ≤ c) (side : x = c + 1 ∨ x + 1 = c) : M4 x 3 c x 6 := by
  rcases side with rfl | hx <;> m4c

set_option maxHeartbeats 4000000 in
/-- Kings opposed three files out, the king on the third rank. -/
theorem m4_o2 {c w : Nat} (hc : 1 ≤ c) (side : w = c + 3 ∨ w + 3 = c) : M4 w 2 c w 5 := by
  rcases side with rfl | hw <;> m4c

set_option maxHeartbeats 4000000 in
/-- The push answered with the king below the sixth rank or on the last rank. -/
theorem s3_push_low {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : S3 a b c e f)
    (fr : Free a b e f c 4) (low : b ≤ 4 ∨ b = 7) : W4 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hf, B, hl, ap, s⟩ := h
  have D' := dom_lift D hl hf ap
  have k1 : Apart a b e f := D.1.k1
  have k2 := D.1.k2
  have k3 := D.1.k3
  have k4' := D'.k4
  have sqf : 4 ≤ f + 1 := s.2.1.2.2
  unfold Free at fr
  by_cases cap : Near e f c 4 ∧ ¬ Near a b c 4
  · exact Or.inl cap
  have step : WeakStep a b c 4 e f e (f + 1) := by
    unfold Lift at hl
    unfold Apart at ap k1
    unfold WeakStep Near Apart Att
    unfold Att at k4'
    omega
  by_cases b7 : b = 7
  · subst b7
    have B7 : B = 7 := by unfold Lift at hl; omega
    subst B7
    exact Or.inr ⟨e, f + 1, step, s⟩
  replace low : b ≤ 4 := by omega
  have hB : B = b + 1 := by unfold Lift at hl; omega
  subst hB
  obtain ⟨nk, sq, rest⟩ := s
  have nk' : ¬ K4 a b c := by unfold K4; omega
  have nb' : ¬ B4 a b c := by
    unfold B4
    unfold K4 at nk
    omega
  refine Or.inr ⟨e, f + 1, step, nk', sq, Or.inr ⟨nb', ?_⟩⟩
  rcases rest with ⟨bes, f5, ee⟩ | ⟨-, op | m | pr | rr⟩
  · unfold B4 at bes
    have b3 : b = 3 := by omega
    subst b3
    rcases ee with rfl | rfl
    · exact Or.inr (Or.inl (by rw [f5]; exact m4_b3 hc bes.2))
    · exact Or.inr (Or.inl (m4_center hc rfl (by omega) nk'))
  · unfold Op4 at op
    have b2 : b = 2 ∧ e = a ∧ f + 1 = 5 ∧ (a = c + 3 ∨ a + 3 = c) := by omega
    obtain ⟨rfl, rfl, f5, side⟩ := b2
    rw [f5]
    exact Or.inr (Or.inl (m4_o2 hc side))
  · exact Or.inr (Or.inl (m4_down low m))
  · exfalso
    obtain ⟨n1, n2, n3⟩ := pr
    apply cap
    refine ⟨by unfold Near at n1 ⊢; omega, fun near => ?_⟩
    have := n3 a b (by unfold Near; omega) (by unfold Near at near ⊢; omega)
    unfold Apart at this
    unfold Near at near n2
    omega
  · exact Or.inr (Or.inr (Or.inr rr))

end EndgameChess.Rules.KPK.Coord
