import EndgameChess.Rules.KPK.Coord.Race

/-! Draws with a bishop or centre pawn on the fifth rank, strong side to move. The lone king
wins the race to each square beside and ahead of the pawn. -/
namespace EndgameChess.Rules.KPK.Coord

/-- The lone king is as close to `(p,q)` as the strong king. -/
def Rc (a b c e f p q : Nat) : Prop := ∀ n, KR a b c p q n → WR e f c p q n

/-- The lone king wins the race to all four key squares. -/
def Rc4 (a b c e f : Nat) : Prop :=
  Rc a b c e f (c + 1) 5 ∧ Rc a b c e f (c + 1) 6 ∧ Rc a b c e f (c - 1) 5 ∧ Rc a b c e f (c - 1) 6

/-- A king two files out on the file `t` is met from the pawn's file. -/
def Oc (a b c e f t : Nat) : Prop :=
  ∀ n, (Ch a b t 5 n ∨ Ch a b t 6 n) → (Ch e f c 5 n ∨ Ch e f c 6 n)

set_option maxHeartbeats 4000000 in
/-- The race to a key square survives a king step and the lone king's step towards it. -/
theorem rc_step {a b c e f x y u v p q : Nat} (hc : 2 ≤ c) (hp : p = c + 1 ∨ p + 1 = c) (hq : q = 5 ∨ q = 6)
    (h : Rc a b c e f p q) (s : Near a b x y) (np : ¬ (x = c ∧ y = 4)) (ap : Apart x y e f)
    (t : Toward e f c 6 u v) (safe : ¬ (v = 5 ∧ (u = c + 1 ∨ u + 1 = c))) : Rc x y c u v p q := by
  intro n kr
  have old := h (n + 1) (kr_step hc hp hq s np kr)
  by_cases zero : n = 0
  · subst zero
    exfalso
    have k1 := kr.1
    have w1 := old.1
    unfold Ch at k1 w1
    unfold Apart at ap
    omega
  · exact wr_step hc hp hq (by omega) t safe old

set_option maxHeartbeats 4000000 in
/-- The same on the outer files. -/
theorem oc_step {a b c e f x y u v t : Nat} (hc : 2 ≤ c) (h : Oc a b c e f t)
    (s : Near a b x y) (st : Toward e f c 6 u v) (mv : ¬ (e = c ∧ f = 6)) : Oc x y c u v t := by
  intro n kr
  have old := h (n + 1) (by
    rcases kr with kr | kr
    · exact Or.inl (ch_step s kr)
    · exact Or.inr (ch_step s kr))
  unfold Ch at *
  unfold Toward at st
  omega

/-- King ahead of the pawn. -/
def K4 (a b c : Nat) : Prop := a ≤ c + 1 ∧ c ≤ a + 1 ∧ (b = 5 ∨ b = 6)

/-- King beside the pawn. -/
def B4 (a b c : Nat) : Prop := b = 4 ∧ (a = c + 1 ∨ a + 1 = c)

/-- The lone king inside the pawn's square. -/
def Sq4 (c e f : Nat) : Prop := e ≤ c + 3 ∧ c ≤ e + 3 ∧ 4 ≤ f

def Ocr (a b c e f : Nat) : Prop := (c < e ∧ e < a ∧ (f ≤ 6 ∨ b ≤ 3)) ∨ Oc a b c e f (c + 2)

def Ocl (a b c e f : Nat) : Prop := (e < c ∧ a < e ∧ (f ≤ 6 ∨ b ≤ 3)) ∨ Oc a b c e f (c - 2)

/-- The lone king wins every race. -/
def M4 (a b c e f : Nat) : Prop := Rc4 a b c e f ∧ Ocr a b c e f ∧ Ocl a b c e f

/-- Kings opposed on a file outside the pawn. -/
def Op4 (a b c e f : Nat) : Prop :=
  e = a ∧ f = 5 ∧ (((c + 2 ≤ a ∨ a + 2 ≤ c) ∧ b = 7) ∨ ((a = c + 3 ∨ a + 3 = c) ∧ b = 3))

/-- The lone king touches the pawn and the king cannot step next to it. -/
def Pr4 (a b c e f : Nat) : Prop :=
  Near e f c 4 ∧ ¬ Near a b c 4 ∧ ∀ x y, Near a b x y → Near x y c 4 → ¬ Apart x y e f

/-- The lone king next to the pawn's rank, the king too far to return. -/
def Rr4 (a c e f : Nat) : Prop := e + 2 = c ∧ f = 4 ∧ c + 4 ≤ a

/-- The fifth-rank draw region of files `c`, `d`. -/
def S4 (a b c e f : Nat) : Prop :=
  ¬ K4 a b c ∧ Sq4 c e f ∧ ((B4 a b c ∧ f = 6 ∧ (e = a ∨ e = c)) ∨
    (¬ B4 a b c ∧ (Op4 a b c e f ∨ M4 a b c e f ∨ Pr4 a b c e f ∨ Rr4 a c e f)))

/-- The lone king's answer at height 4. -/
def W4 (a b c e f : Nat) : Prop :=
  Capture a b c 4 e f ∨ ∃ x y, WeakStep a b c 4 e f x y ∧ S4 a b c x y

theorem ocr_step {a b c e f x y u v : Nat} (h : Ocr a b c e f) (s : Near a b x y)
    (st : Toward e f c 6 u v) (mv : ¬ (e = c ∧ f = 6)) (hc : 2 ≤ c) (hf : 4 ≤ f ∧ f ≤ 7) : Ocr x y c u v := by
  rcases h with ⟨h1, h2, h3⟩ | h
  · by_cases g : c < u
    · left
      unfold Near at s
      unfold Toward at st
      omega
    · right
      intro n _
      unfold Toward at st
      unfold Ch
      omega
  · exact Or.inr (oc_step hc h s st mv)

theorem ocl_step {a b c e f x y u v : Nat} (h : Ocl a b c e f) (s : Near a b x y)
    (st : Toward e f c 6 u v) (mv : ¬ (e = c ∧ f = 6)) (hc : 2 ≤ c) (hf : 4 ≤ f ∧ f ≤ 7) : Ocl x y c u v := by
  rcases h with ⟨h1, h2, h3⟩ | h
  · by_cases g : u < c
    · left
      unfold Near at s
      unfold Toward at st
      omega
    · right
      intro n _
      unfold Toward at st
      unfold Ch
      omega
  · exact Or.inr (oc_step hc h s st mv)

/-- The main race survives a king step. -/
theorem m4_step {a b c e f x y u v : Nat} (hc : 2 ≤ c) (h : M4 a b c e f) (s : Near a b x y)
    (np : ¬ (x = c ∧ y = 4)) (ap : Apart x y e f) (st : Toward e f c 6 u v)
    (safe : ¬ (v = 5 ∧ (u = c + 1 ∨ u + 1 = c))) (mv : ¬ (e = c ∧ f = 6))
    (hf : 4 ≤ f ∧ f ≤ 7) : M4 x y c u v := by
  obtain ⟨⟨r1, r2, r3, r4⟩, o1, o2⟩ := h
  exact ⟨⟨rc_step hc (Or.inl rfl) (Or.inl rfl) r1 s np ap st safe,
    rc_step hc (Or.inl rfl) (Or.inr rfl) r2 s np ap st safe,
    rc_step hc (Or.inr (by omega)) (Or.inl rfl) r3 s np ap st safe,
    rc_step hc (Or.inr (by omega)) (Or.inr rfl) r4 s np ap st safe⟩,
    ocr_step o1 s st mv hc hf, ocl_step o2 s st mv hc hf⟩

/-- The race read off at distance one. -/
theorem rc1 {a b c e f p q : Nat} (hc : 2 ≤ c) (hp : p = c + 1 ∨ p + 1 = c) (h : Rc a b c e f p q) :
    ¬ Ch a b p q 1 ∨ Ch e f p q 1 := by
  by_cases g : Ch a b p q 1
  · right
    refine (h 1 ⟨g, Or.inl ?_⟩).1
    unfold Ch at g
    unfold Thru
    omega
  · exact Or.inl g

/-- The race to a square one rank further, read off at distance two. -/
theorem rc2 {a b c e f p : Nat} (hc : 2 ≤ c) (hp : p = c + 1 ∨ p + 1 = c) (h : Rc a b c e f p 6) :
    ¬ Ch a b p 6 2 ∨ WR e f c p 6 2 := by
  by_cases g : Ch a b p 6 2
  · right
    exact h 2 ⟨g, Or.inl (by unfold Thru; omega)⟩
  · exact Or.inl g

/-- On the pawn's file ahead of it the lone king wins every race the king has not won. -/
theorem m4_center {x y c u v : Nat} (hc : 2 ≤ c) (hu : u = c) (hv : v = 5 ∨ v = 6) (k : ¬ K4 x y c) :
    M4 x y c u v := by
  subst hu
  unfold K4 at k
  have rc (p q : Nat) (hp : p = u + 1 ∨ p + 1 = u) (hq : q = 5 ∨ q = 6) : Rc x y u u v p q := by
    intro n kr
    obtain ⟨k1, -⟩ := kr
    unfold Ch at k1
    refine ⟨by unfold Ch; omega, Or.inl ?_⟩
    unfold Cross
    omega
  refine ⟨⟨rc _ _ (Or.inl rfl) (Or.inl rfl), rc _ _ (Or.inl rfl) (Or.inr rfl),
    rc _ _ (Or.inr (by omega)) (Or.inl rfl), rc _ _ (Or.inr (by omega)) (Or.inr rfl)⟩, Or.inr ?_, Or.inr ?_⟩
  all_goals
    intro n _
    unfold Ch
    omega

theorem s4_center {x y c u v : Nat} (hc : 2 ≤ c) (hu : u = c) (hv : v = 5 ∨ v = 6) (k : ¬ K4 x y c)
    (b : ¬ B4 x y c) : S4 x y c u v :=
  ⟨k, by unfold Sq4; omega, Or.inr ⟨b, Or.inr (Or.inl (m4_center hc hu hv k))⟩⟩

set_option maxHeartbeats 4000000 in
/-- The lone king touching a pawn that the king cannot reach takes it. -/
theorem w4_take {a b c e f x y : Nat} (h : Pr4 a b c e f) (s : Near a b x y) (ap : Apart x y e f) :
    W4 x y c e f := by
  obtain ⟨n1, n2, n3⟩ := h
  by_cases g : Near x y c 4
  · exact absurd ap (n3 x y s g)
  · exact Or.inl ⟨n1, g⟩

/-- The default reply: one step towards the square two ahead of the pawn. -/
theorem toward_exists (e f c : Nat) : ∃ u v, Toward e f c 6 u v := by
  have hx : ∃ u, (e < c ∧ u = e + 1) ∨ (c < e ∧ u + 1 = e) ∨ (e = c ∧ u = e) := by
    rcases Nat.lt_trichotomy e c with g | g | g
    · exact ⟨e + 1, Or.inl ⟨g, rfl⟩⟩
    · exact ⟨e, Or.inr (Or.inr ⟨g, rfl⟩)⟩
    · exact ⟨e - 1, Or.inr (Or.inl ⟨g, by omega⟩)⟩
  have hy : ∃ v, (f < 6 ∧ v = f + 1) ∨ (6 < f ∧ v + 1 = f) ∨ (f = 6 ∧ v = f) := by
    rcases Nat.lt_trichotomy f 6 with g | g | g
    · exact ⟨f + 1, Or.inl ⟨g, rfl⟩⟩
    · exact ⟨f, Or.inr (Or.inr ⟨g, rfl⟩)⟩
    · exact ⟨f - 1, Or.inr (Or.inl ⟨g, by omega⟩)⟩
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  exact ⟨u, v, hu, hv⟩

set_option maxHeartbeats 4000000 in
/-- A king winning no race cannot step ahead of the pawn. -/
theorem k4_step {a b c e f x y : Nat} (hc : 2 ≤ c) (h : M4 a b c e f) (nb : ¬ B4 a b c) (nk : ¬ K4 a b c)
    (s : Near a b x y) (ap : Apart x y e f) (k1 : Apart a b e f) (k2 : ¬ (a = c ∧ b = 4)) : ¬ K4 x y c := by
  intro q
  obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := h
  have land (p q' : Nat) (hp : p = c + 1 ∨ p + 1 = c) (r : Rc a b c e f p q') (e1 : x = p) (e2 : y = q') : False := by
    subst e1 e2
    rcases rc1 hc hp r with g | g
    · apply g
      unfold Ch
      unfold Near at s
      omega
    · unfold Ch at g
      unfold Apart at ap
      omega
  unfold K4 at q nk
  unfold B4 at nb
  by_cases g1 : x = c + 1
  · rcases q.2.2 with g | g
    · exact land _ _ (Or.inl rfl) r1 g1 g
    · exact land _ _ (Or.inl rfl) r2 g1 g
  by_cases g2 : x + 1 = c
  · have g3 : x = c - 1 := by omega
    rcases q.2.2 with g | g
    · exact land _ _ (Or.inr (by omega)) r3 g3 g
    · exact land _ _ (Or.inr (by omega)) r4 g3 g
  have g3 : x = c := by omega
  subst g3
  unfold Near at s
  rcases q.2.2 with g | g
  · subst g
    have k2' := k2
    omega
  · subst g
    have top : b = 7 := by omega
    subst top
    have z1 := rc1 hc (Or.inl rfl) r2
    have z2 := rc1 hc (Or.inr (by omega)) r4
    have z3 := rc2 hc (Or.inl rfl) r2
    have z4 := rc2 hc (Or.inr (by omega)) r4
    clear r1 r2 r3 r4 land
    unfold WR Cross Hit Ch at z3 z4
    unfold Ch at z1 z2
    unfold Apart at ap k1
    omega

set_option maxHeartbeats 4000000 in
/-- The main race: the default reply is legal and stays in the region. -/
theorem w4_main {a b c e f x y : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (h : M4 a b c e f)
    (st : KingStep a b c 4 e f x y) (nb : ¬ B4 a b c) (nk : ¬ K4 a b c) (sq : Sq4 c e f)
    (mv : ¬ (e = c ∧ f = 6)) (n24 : ¬ (f = 4 ∧ (e = c + 2 ∨ e + 2 = c)))
    (free : ∀ u v, Toward e f c 6 u v → Apart x y u v) : W4 x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  obtain ⟨u, v, tw⟩ := toward_exists e f c
  have ap := free u v tw
  have s0 := st.1
  have np := st.k6
  have ap0 : Apart x y e f := st.2.2.2.2
  have k3 := D.1.k3
  have k4 := D.k4
  have m := id h
  obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := m
  have a1 := rc1 hc (Or.inl rfl) r1
  have a2 := rc1 hc (Or.inl rfl) r2
  have a3 := rc1 hc (Or.inr (by omega)) r3
  have a4 := rc1 hc (Or.inr (by omega)) r4
  clear r1 r2 r3 r4
  unfold Sq4 at sq
  have tw' := tw
  unfold Toward at tw'
  have safe : ¬ (v = 5 ∧ (u = c + 1 ∨ u + 1 = c)) := by omega
  have new := m4_step hc h s0 np ap0 tw safe mv (by omega)
  have sq' : Sq4 c u v := by unfold Sq4; omega
  have kx : ¬ K4 x y c := k4_step hc h nb nk s0 ap0 (by have := D.1.k1; exact this) D.1.k2
  clear a1 a2 a3 a4
  by_cases bx : B4 x y c
  · have bx' := bx
    unfold B4 at bx'
    obtain ⟨rfl, side⟩ := bx'
    have near4 : Ch a b x 4 1 := by unfold Ch; unfold Near at s0; omega
    have fin : v = 6 ∧ (u = x ∨ u = c) := by
      rcases side with g | g
      · have w5 : WR e f c (c + 1) 5 2 := by
          refine h.1.1 2 ⟨by unfold Ch at near4 ⊢; omega, Or.inl ?_⟩
          unfold Ch at near4; unfold Thru; omega
        have w7 : Ch e f c 5 2 ∨ Ch e f c 6 2 ∨ e = c + 1 := by
          rcases h.2.1 with q | q
          · unfold Ch at near4; omega
          · rcases q 2 (Or.inl (by unfold Ch at near4 ⊢; omega)) with q | q
            · exact Or.inl q
            · exact Or.inr (Or.inl q)
        clear h new s0 st nb nk free
        unfold WR Cross Hit Ch at w5
        unfold Ch at w7 near4
        unfold Apart at ap0
        omega
      · have w5 : WR e f c (c - 1) 5 2 := by
          refine h.1.2.2.1 2 ⟨by unfold Ch at near4 ⊢; omega, Or.inl ?_⟩
          unfold Ch at near4; unfold Thru; omega
        have w7 : Ch e f c 5 2 ∨ Ch e f c 6 2 ∨ e + 1 = c := by
          rcases h.2.2 with q | q
          · unfold Ch at near4; omega
          · rcases q 2 (Or.inl (by unfold Ch at near4 ⊢; omega)) with q | q
            · exact Or.inl q
            · exact Or.inr (Or.inl q)
        clear h new s0 st nb nk free
        unfold WR Cross Hit Ch at w5
        unfold Ch at w7 near4
        unfold Apart at ap0
        omega
    refine Or.inr ⟨u, v, ⟨?_, by omega, by omega, ?_, ap, ?_⟩, kx, sq', Or.inl ⟨bx, fin.1, fin.2⟩⟩
    · unfold Near; omega
    · omega
    · unfold Att; omega
  · refine Or.inr ⟨u, v, ⟨?_, by omega, by omega, ?_, ap, ?_⟩, kx, sq', Or.inr ⟨bx, Or.inr (Or.inl new)⟩⟩
    · unfold Near; omega
    · omega
    · unfold Att; omega

set_option maxHeartbeats 4000000 in
/-- Directly ahead of the pawn the lone king steps back to the pawn or opposes the king. -/
theorem w4_c6 {c x y : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7)
    (ap : Apart x y c 6) (np : ¬ (x = c ∧ y = 4)) : W4 x y c c 6 := by
  unfold Apart at ap
  have kx : ¬ K4 x y c := by unfold K4; omega
  by_cases bx : B4 x y c
  · have b' := bx
    unfold B4 at b'
    refine Or.inr ⟨x, 6, by unfold WeakStep Near Apart Att; omega, kx, ?_, Or.inl ⟨bx, rfl, Or.inl rfl⟩⟩
    unfold Sq4; omega
  · refine Or.inr ⟨c, 5, ?_, s4_center hc rfl (Or.inl rfl) kx bx⟩
    unfold B4 at bx
    unfold WeakStep Near Apart Att
    omega

set_option maxHeartbeats 4000000 in
/-- The king beside the pawn moves away from direct opposition. -/
theorem w4_bes {a c e x y : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7) (side : a = c + 1 ∨ a + 1 = c)
    (he : e = a) (s : Near a 4 x y) (ap : Apart x y e 6) (np : ¬ (x = c ∧ y = 4)) : W4 x y c e 6 := by
  subst he
  unfold Near at s
  unfold Apart at ap
  have kx : ¬ K4 x y c := by unfold K4; omega
  have bx : ¬ B4 x y c := by unfold B4; omega
  exact Or.inr ⟨c, 6, by unfold WeakStep Near Apart Att; omega, s4_center hc rfl (Or.inr rfl) kx bx⟩

/-- A distant lone king on the far side steps next to the pawn, out of the king's reach. -/
theorem w4_far {a b c x y : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7) (far : c + 4 ≤ a)
    (s : Near a b x y) : W4 x y c (c - 2) 4 := by
  unfold Near at s
  refine Or.inr ⟨c - 1, 4, by unfold WeakStep Near Apart Att; omega, ?_, ?_, Or.inr ⟨?_, Or.inr (Or.inr (Or.inl ?_))⟩⟩
  · unfold K4; omega
  · unfold Sq4; omega
  · unfold B4; omega
  · refine ⟨by unfold Near; omega, by unfold Near; omega, ?_⟩
    intro p q n1 n2
    unfold Near at n1 n2
    omega

/-- From two files out on the pawn's rank the lone king steps beside the pawn. These are
the races it keeps. -/
theorem rc_t5 {x y c t o u : Nat} (sd : Sd c t o u) (k : ¬ Ch x y t 5 0) : Rc x y c t 4 t 5 := by
  intro n kr
  obtain ⟨k1, -⟩ := kr
  unfold Sd at sd
  unfold Ch at k k1
  refine ⟨by unfold Ch; omega, Or.inl ?_⟩
  unfold Cross
  omega

theorem rc_t6 {x y c t o u : Nat} (sd : Sd c t o u) (k : ¬ Ch x y t 6 1) : Rc x y c t 4 t 6 := by
  intro n kr
  obtain ⟨k1, -⟩ := kr
  unfold Sd at sd
  unfold Ch at k k1
  refine ⟨by unfold Ch; omega, Or.inl ?_⟩
  unfold Cross
  omega

set_option maxHeartbeats 4000000 in
theorem rc_o {a b c t o u x y q : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (hq : q = 5 ∨ q = 6)
    (h : Rc a b c u 4 o q) (s : Near a b x y) (np : ¬ (x = c ∧ y = 4)) : Rc x y c t 4 o q := by
  intro n kr
  have sd' := sd
  unfold Sd at sd'
  have hp : o = c + 1 ∨ o + 1 = c := by omega
  have old := h (n + 1) (kr_step hc hp hq s np kr)
  unfold WR Cross Hit Ch at *
  omega

end EndgameChess.Rules.KPK.Coord
