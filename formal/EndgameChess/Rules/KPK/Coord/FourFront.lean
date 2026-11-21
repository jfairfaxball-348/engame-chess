import EndgameChess.Rules.KPK.Coord.FourFace

/-! Fourth rank, the winning side: the race for the opposition. The front squares of a
pawn on `(c,3)` are the three squares `(p,4)` one rank ahead of it. A king on a front
square wins unless the lone king stands two squares above it on the same file, where it
holds the opposition. So the king wins if it reaches a front square before the lone king
reaches the square two above it, provided the pawn cannot fall on the way and the king
does not have to pass in front of a lone king on its own side of the pawn.

Two pawn advances are needed on the way: a lone king below the pawn's rank never catches
the pawn, and with the two kings beside the pawn on opposite sides the king wins the race
to the key square on its side. -/
namespace EndgameChess.Rules.KPK.Coord

/-- A lone king below the pawn's rank lets the pawn advance. -/
theorem low_push {a b c e f : Nat} (hf : f ≤ 2)
    (nb : ¬ (a = c ∧ b = 4)) : PushOK3 a b c e f := by
  refine ⟨⟨nb, by omega⟩, ?_, ?_⟩
  · unfold Capture Near
    omega
  · intro X Y st s
    obtain ⟨⟨m1, m2, m3, m4⟩, m5, m6⟩ := WeakStep.bounds st
    obtain ⟨-, sq, -⟩ := s
    unfold Sq4 at sq
    omega

/-- The king and the lone king beside the pawn on its rank, on opposite sides. -/
def Side3 (a b c e f : Nat) : Prop :=
  b = 3 ∧ f = 3 ∧ ((a = c + 1 ∧ e + 1 = c) ∨ (a + 1 = c ∧ e = c + 1))

set_option maxHeartbeats 4000000 in
/-- With the two kings beside the pawn on opposite sides, the pawn advances: the king
still guards it, and it reaches the key square on its side two steps ahead of a lone king
that must go round the pawn. -/
theorem side_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : Side3 a b c e f) :
    PushOK3 a b c e f := by
  obtain ⟨rfl, rfl, hs⟩ := h
  refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
  · unfold Capture Near
    omega
  · intro X Y st s
    obtain ⟨⟨m1, m2, m3, m4⟩, m5, m6⟩ := WeakStep.bounds st
    have k6 := st.k6
    obtain ⟨-, sq, hb | ⟨-, op | m4 | pr | rr⟩⟩ := s
    · exact absurd hb.1 (by unfold B4; omega)
    · unfold Op4 at op
      omega
    · unfold Sq4 at sq
      obtain ⟨⟨r1, -, r3, -⟩, -, -⟩ := m4
      rcases hs with ⟨rfl, he⟩ | ⟨ha, rfl⟩
      · have w := r1 2 (by unfold KR Thru Ch; omega)
        unfold WR Cross Hit Ch at w
        omega
      · have w := r3 2 (by unfold KR Thru Ch; omega)
        unfold WR Cross Hit Ch at w
        omega
    · exact pr.2.1 (by unfold Near; omega)
    · unfold Rr4 at rr
      omega

/-- The king must pass in front of a lone king on its own side of the pawn. -/
def Xc (a c e p : Nat) : Prop := (c < a ∧ c < e ∧ p < c) ∨ (a < c ∧ e < c ∧ c < p)

/-- The only shortest way to the front square `(p,4)` runs through the pawn. -/
def Thr4 (a b c p : Nat) : Prop :=
  (p = c + 1 ∧ a + 3 = c + b ∧ a < c) ∨ (p + 1 = c ∧ a + b = c + 3 ∧ c < a)

/-- The king's step towards the front square `(p,4)`: straight towards it, or beside the
pawn when that step would land on the pawn. -/
def FMv (a b c e p x y : Nat) : Prop :=
  (Toward a b p 4 x y ∧ ¬ (x = c ∧ y = 3)) ∨
  (Toward a b p 4 c 3 ∧ y = 3 ∧
    ((¬ a = c ∧ x = a) ∨ (a = c ∧ c < e ∧ x + 1 = c) ∨ (a = c ∧ e ≤ c ∧ x = c + 1)))

/-- That step is legal, leaves the pawn safe and comes one step nearer. -/
def FGo (m a b c e f p : Nat) : Prop :=
  ∃ x y, FMv a b c e p x y ∧ Apart x y e f ∧ ¬ Capture x y c 3 e f ∧ Ch x y p 4 (m - 1)

/-- The king is exactly `m` steps from the front square `(p,4)`, the lone king is more than
`m` steps from the square `(p,6)` two above it, the pawn cannot fall first, the king need
not pass in front of the lone king or through the pawn, and from two steps out the next
step is legal. -/
def Front3 (m a b c e f p : Nat) : Prop :=
  (p = c + 1 ∨ p = c ∨ p + 1 = c) ∧ Ch a b p 4 m ∧ (m = 0 ∨ ¬ Ch a b p 4 (m - 1)) ∧
    ¬ Ch e f p 6 m ∧ (¬ Ch e f c 3 m ∨ Near a b c 3 ∨ Nr a b c e f) ∧ ¬ Xc a c e p ∧
    ¬ Thr4 a b c p ∧ (m ≤ 1 ∨ FGo m a b c e f p)

set_option maxHeartbeats 4000000 in
/-- On a front square, with the lone king not two squares above, the king wins the race to
a key square next to it, or faces the lone king from the square in front of the pawn. -/
theorem front0 {a b c e f p : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : Front3 0 a b c e f p) :
    (∃ q, Key3 1 a b c e f q) ∨ Face 2 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, hk, -, hl, -⟩ := h
  have k1 := D.1.k1
  have g : Near a b c 3 := by
    unfold Ch at hk
    unfold Near
    omega
  have hq : (Ch a b (c - 1) 5 1 ∧ ¬ Ch e f (c - 1) 5 1) ∨ (Ch a b c 5 1 ∧ ¬ Ch e f c 5 1) ∨
      (Ch a b (c + 1) 5 1 ∧ ¬ Ch e f (c + 1) 5 1) ∨
      (e = c ∧ f = 6 ∧ (a = c + 1 ∨ a + 1 = c) ∧ b = 4) := by
    unfold Ch at *
    omega
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨rfl, rfl, ha, rfl⟩
  · exact Or.inl ⟨c - 1, Or.inr (Or.inr (by omega)), h1, h2, Or.inr (Or.inl g)⟩
  · exact Or.inl ⟨c, Or.inr (Or.inl rfl), h1, h2, Or.inr (Or.inl g)⟩
  · exact Or.inl ⟨c + 1, Or.inl rfl, h1, h2, Or.inr (Or.inl g)⟩
  · refine Or.inr ⟨4, rfl, Or.inl rfl, by omega, by omega, by unfold Near; omega, ?_⟩
    unfold FC
    omega

/-- The seven outcomes of a blocked step onto a front square. -/
def BlkOut (a b c e f : Nat) : Prop :=
  (Ch a b (c - 1) 5 1 ∧ ¬ Ch e f (c - 1) 5 1 ∧ (¬ Ch e f c 3 1 ∨ Near a b c 3)) ∨
    (Ch a b c 5 1 ∧ ¬ Ch e f c 5 1 ∧ (¬ Ch e f c 3 1 ∨ Near a b c 3)) ∨
    (Ch a b (c + 1) 5 1 ∧ ¬ Ch e f (c + 1) 5 1 ∧ (¬ Ch e f c 3 1 ∨ Near a b c 3)) ∨
    Ch a b (c - 1) 5 0 ∨ Ch a b c 5 0 ∨ Ch a b (c + 1) 5 0 ∨ Side3 a b c e f

theorem blk_key {a b c e f q : Nat} (hc : 1 ≤ c) (hq : q + 1 = c ∨ q = c ∨ q = c + 1)
    (h : Ch a b q 5 1 ∧ ¬ Ch e f q 5 1 ∧ (¬ Ch e f c 3 1 ∨ Near a b c 3)) : BlkOut a b c e f := by
  rcases hq with hq | rfl | rfl
  · have : q = c - 1 := by omega
    subst this
    exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem blk_on {a b c e f q : Nat} (hc : 1 ≤ c) (hq : q + 1 = c ∨ q = c ∨ q = c + 1)
    (h : Ch a b q 5 0) : BlkOut a b c e f := by
  rcases hq with hq | rfl | rfl
  · have : q = c - 1 := by omega
    subst this
    exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

set_option maxHeartbeats 4000000 in
/-- The local geometry of a blocked step onto a front square: on the pawn's rank the two
kings stand beside the pawn; otherwise the king is on a key square or next to one that
the lone king does not guard. -/
theorem blk_geo {a b c e f x d : Nat} (hc : 1 ≤ c) (hf : 3 ≤ f)
    (hp : x = c + 1 ∨ x = c ∨ x + 1 = c)
    (hk : Ch a b x 4 1) (ex : ¬ Ch a b x 4 0) (hl : ¬ Ch e f x 6 1) (ne : Ch e f x 4 1)
    (k1 : a + 2 ≤ e ∨ e + 2 ≤ a ∨ b + 2 ≤ f ∨ f + 2 ≤ b) (k2 : ¬ (a = c ∧ b = 3))
    (k3 : ¬ (e = c ∧ f = 3)) (k4 : ¬ (f = 3 + 1 ∧ (e = c + 1 ∨ e + 1 = c)))
    (sf : ¬ Ch e f c 3 1 ∨ Near a b c 3 ∨ (Ch a b c 3 d ∧ ¬ Ch e f c 3 (d - 1))) :
    BlkOut a b c e f := by
  unfold Ch at hk ex hl ne
  have sf' : ¬ (e ≤ c + 1 ∧ c ≤ e + 1 ∧ f ≤ 4) ∨ Near a b c 3 := by
    rcases sf with sf | sf | ⟨kd, ld⟩
    · left
      unfold Ch at sf
      omega
    · exact Or.inr sf
    · unfold Ch at kd ld
      unfold Near
      omega
  clear sf
  have hb : b = 3 ∨ b = 4 ∨ b = 5 := by omega
  unfold Near at sf'
  rcases hb with rfl | rfl | rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    unfold Side3
    omega
  · have ha : a + 1 = x ∨ a = x + 1 := by omega
    rcases ha with ha | ha
    · refine blk_key (q := a) hc (by omega) ⟨by unfold Ch; omega, by unfold Ch; omega, ?_⟩
      unfold Near
      unfold Ch
      omega
    · refine blk_key (q := a) hc (by omega) ⟨by unfold Ch; omega, by unfold Ch; omega, ?_⟩
      unfold Near
      unfold Ch
      omega
  · by_cases ka : a + 1 = c ∨ a = c ∨ a = c + 1
    · exact blk_on (q := a) hc ka (by unfold Ch; omega)
    · refine blk_key (q := x) hc (by omega) ⟨by unfold Ch; omega, by unfold Ch; omega, ?_⟩
      unfold Near
      unfold Ch
      omega

set_option maxHeartbeats 4000000 in
/-- One step from a front square, when the step onto it is blocked by the lone king, the
king wins the race to a key square, or the two kings stand beside the pawn. -/
theorem front1_block {a b c e f p x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (hf : 3 ≤ f)
    (h : Front3 1 a b c e f p) (mv : FMv a b c e p x y)
    (bl : ¬ (Apart x y e f ∧ ¬ Capture x y c 3 e f)) :
    (∃ q n, n ≤ 1 ∧ Key3 n a b c e f q) ∨ Side3 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, hk, ex, hl, hs, nx, nt, -⟩ := h
  have hxy : x = p ∧ y = 4 := by
    unfold Ch at hk ex
    rcases mv with ⟨tw, -⟩ | ⟨tw, -⟩ <;> (unfold Toward at tw; omega)
  obtain ⟨rfl, rfl⟩ := hxy
  have ne : Ch e f x 4 1 := by
    have nc : ¬ Capture x 4 c 3 e f := fun cp => cp.2 (by unfold Near; omega)
    have na : ¬ Apart x 4 e f := fun ap => bl ⟨ap, nc⟩
    unfold Apart at na
    unfold Ch
    omega
  clear mv bl nx nt u1 u2 u3 u4 u5 u6 u7
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  have k2 := D.1.k2
  have hq : BlkOut a b c e f := by
    have ex' : ¬ Ch a b x 4 0 := ex.resolve_left (by omega)
    rcases hs with hs | hs | ⟨d, kd, ld⟩
    · exact blk_geo (d := 0) hc hf hp hk ex' hl ne k1 k2 k3 k4
        (Or.inl (fun g => hs (by unfold Ch at *; omega)))
    · exact blk_geo (d := 0) hc hf hp hk ex' hl ne k1 k2 k3 k4 (Or.inr (Or.inl hs))
    · exact blk_geo hc hf hp hk ex' hl ne k1 k2 k3 k4 (Or.inr (Or.inr ⟨kd, ld⟩))
  have z (q : Nat) (hq : q = c + 1 ∨ q = c ∨ q + 1 = c) (h1 : Ch a b q 5 0) :
      (∃ q n, n ≤ 1 ∧ Key3 n a b c e f q) ∨ Side3 a b c e f := by
    refine Or.inl ⟨q, 0, by omega, hq, h1, ?_, Or.inl ?_⟩
    · unfold Ch at h1 ⊢
      omega
    · unfold Ch
      omega
  unfold BlkOut at hq
  rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h1 | h1 | h1 | h
  · exact Or.inl ⟨c - 1, 1, Nat.le_refl _, Or.inr (Or.inr (by omega)), h1, h2,
      h3.elim Or.inl (fun g => Or.inr (Or.inl g))⟩
  · exact Or.inl ⟨c, 1, Nat.le_refl _, Or.inr (Or.inl rfl), h1, h2,
      h3.elim Or.inl (fun g => Or.inr (Or.inl g))⟩
  · exact Or.inl ⟨c + 1, 1, Nat.le_refl _, Or.inl rfl, h1, h2,
      h3.elim Or.inl (fun g => Or.inr (Or.inl g))⟩
  · exact z (c - 1) (Or.inr (Or.inr (by omega))) h1
  · exact z c (Or.inr (Or.inl rfl)) h1
  · exact z (c + 1) (Or.inl rfl) h1
  · exact Or.inr h

/-- From next to the pawn, the step towards a front square stays next to it. -/
theorem fmv_near {a b c e p x y : Nat} (hc : 1 ≤ c) (hp : p = c + 1 ∨ p = c ∨ p + 1 = c)
    (mv : FMv a b c e p x y) (hs : Near a b c 3) : Near x y c 3 := by
  unfold FMv Toward at mv
  unfold Near at *
  omega

/-- A king not next to the pawn, but no farther from it than from the front square, comes
one step nearer the pawn with the step towards the front square. -/
theorem fmv_closer {m a b c p x y d : Nat} (hp : p = c + 1 ∨ p = c ∨ p + 1 = c)
    (hk : Ch a b p 4 (m + 1)) (ex : ¬ Ch a b p 4 m) (kd : Ch a b c 3 d) (dm : d ≤ m + 1)
    (nn : ¬ Near a b c 3) (npw : ¬ (a = c ∧ b = 3)) (tw : Toward a b p 4 x y) :
    Ch x y c 3 (d - 1) ∧ 2 ≤ d ∧ ¬ (x = c ∧ y = 3) := by
  unfold Ch at hk ex kd ⊢
  unfold Near at nn
  unfold Toward at tw
  omega

set_option maxHeartbeats 4000000 in
/-- Three or more steps from the front square the step towards it is always legal and
leaves the pawn safe. -/
theorem go_auto {d a b c e f p : Nat} (h3 : c ≤ 3) (ha : a ≤ 7) (hb : b ≤ 7)
    (he : e ≤ 7) (hf7 : f ≤ 7) (hf : 3 ≤ f) (hd : 3 ≤ d) (hp : p = c + 1 ∨ p = c ∨ p + 1 = c)
    (hk : Ch a b p 4 d) (ex : ¬ Ch a b p 4 (d - 1)) (hl : ¬ Ch e f p 6 d)
    (hs : ¬ Ch e f c 3 d ∨ Near a b c 3 ∨ Nr a b c e f)
    (k1 : a + 2 ≤ e ∨ e + 2 ≤ a ∨ b + 2 ≤ f ∨ f + 2 ≤ b) (k3 : ¬ (e = c ∧ f = 3))
    (k4 : ¬ (f = 3 + 1 ∧ (e = c + 1 ∨ e + 1 = c))) : FGo d a b c e f p := by
  obtain ⟨x, y, tw⟩ := toward_ex a b p 4
  have far : ¬ (x = c ∧ y = 3) ∧ Ch x y p 4 (d - 1) := by
    unfold Ch at hk ex ⊢
    unfold Toward at tw
    omega
  refine ⟨x, y, Or.inl ⟨tw, far.1⟩, ?_, ?_, far.2⟩
  · unfold Ch at hk ex hl
    unfold Toward at tw
    unfold Apart
    omega
  · rintro ⟨cn, cg⟩
    rcases hs with hs | hs | ⟨d', kd, ld⟩
    · unfold Ch at hs hk
      unfold Near at cn
      omega
    · unfold Ch at hk ex
      unfold Toward at tw
      unfold Near at hs cg
      omega
    · unfold Ch at kd ld hk ex
      unfold Toward at tw
      unfold Near at cn cg
      omega

/-- The step towards the front square never makes the king pass in front of a lone king on
its own side, when the lone king is on or above the pawn's rank and loses the race. -/
theorem xc_keep {m a b c e f p x y X Y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a ≤ 7) (hb : b ≤ 7)
    (he : e ≤ 7) (hf7 : f ≤ 7) (hp : p = c + 1 ∨ p = c ∨ p + 1 = c) (hf : 3 ≤ f)
    (hk : Ch a b p 4 (m + 1)) (ex : ¬ Ch a b p 4 m) (hl : ¬ Ch e f p 6 (m + 1))
    (nx : ¬ Xc a c e p) (mv : FMv a b c e p x y) (hX : X ≤ e + 1 ∧ e ≤ X + 1)
    (hY : Y ≤ f + 1 ∧ f ≤ Y + 1) (ap : x + 2 ≤ X ∨ X + 2 ≤ x ∨ y + 2 ≤ Y ∨ Y + 2 ≤ y) :
    ¬ Xc x c X p := by
  unfold Xc at nx ⊢
  unfold Ch at hk ex hl
  rcases mv with ⟨tw, -⟩ | ⟨tw, hy3, h⟩
  · unfold Toward at tw
    omega
  · unfold Toward at tw
    omega

/-- Nor does it make the only way to the front square run through the pawn. -/
theorem thr_keep {m a b c e p x y : Nat} (hp : p = c + 1 ∨ p = c ∨ p + 1 = c)
    (hk : Ch a b p 4 (m + 1)) (ex : ¬ Ch a b p 4 m) (nt : ¬ Thr4 a b c p)
    (mv : FMv a b c e p x y) : ¬ Thr4 x y c p := by
  unfold Thr4 at nt ⊢
  unfold Ch at hk ex
  rcases mv with ⟨tw, -⟩ | ⟨tw, hy3, h⟩
  · unfold Toward at tw
    omega
  · unfold Toward at tw
    omega

set_option maxHeartbeats 4000000 in
/-- Two steps from the front square, with the lone king at least three files from it, the
step towards the front square is legal and leaves the pawn safe. -/
theorem go_two_core {c p x y X Y u v : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (hx : x ≤ 7)
    (hy : y ≤ 7) (hp : p = c + 1 ∨ p = c ∨ p + 1 = c)
    (dx : Ch x y p 4 2) (ex : ¬ Ch x y p 4 1) (far : X + 3 ≤ p ∨ p + 3 ≤ X)
    (nt : ¬ Thr4 x y c p) (npw : ¬ (x = c ∧ y = 3))
    (a7 : x + 2 ≤ X ∨ X + 2 ≤ x ∨ y + 2 ≤ Y ∨ Y + 2 ≤ y)
    (k6 : ¬ (X = c ∧ Y = 3)) (k8 : ¬ (Y = 3 + 1 ∧ (X = c + 1 ∨ X + 1 = c))) (hY : 3 ≤ Y)
    (mv : FMv x y c X p u v) :
    Apart u v X Y ∧ ¬ Capture u v c 3 X Y ∧ Ch u v p 4 1 := by
  unfold Ch at dx ex
  unfold Thr4 at nt
  unfold Apart Capture Ch Near
  rcases mv with ⟨tw2, np2⟩ | ⟨tw2, rfl, hx2⟩
  · unfold Toward at tw2
    rcases hp with rfl | rfl | hp <;> omega
  · unfold Toward at tw2
    rcases hp with rfl | rfl | hp <;> omega

/-- The step from two out exists in the form the class asks for. -/
theorem fmv_ex (x y c X p : Nat) (hc : 1 ≤ c) : ∃ u v, FMv x y c X p u v := by
  obtain ⟨u, v, tw⟩ := toward_ex x y p 4
  by_cases pw : u = c ∧ v = 3
  · obtain ⟨rfl, rfl⟩ := pw
    by_cases g : x = u
    · by_cases g2 : u < X
      · exact ⟨u - 1, 3, Or.inr ⟨tw, rfl, Or.inr (Or.inl ⟨g, g2, by omega⟩)⟩⟩
      · exact ⟨u + 1, 3, Or.inr ⟨tw, rfl, Or.inr (Or.inr ⟨g, by omega, rfl⟩)⟩⟩
    · exact ⟨x, 3, Or.inr ⟨tw, rfl, Or.inl ⟨g, rfl⟩⟩⟩
  · exact ⟨u, v, Or.inl ⟨tw, pw⟩⟩

/-- The step towards the front square is a king step. -/
theorem fmv_near_step {m a b c e p x y : Nat} (hc : 1 ≤ c) (hp : p = c + 1 ∨ p = c ∨ p + 1 = c)
    (hk : Ch a b p 4 (m + 1)) (ex : ¬ Ch a b p 4 m) (mv : FMv a b c e p x y) :
    Near a b x y ∧ ¬ (x = c ∧ y = 3) := by
  unfold Ch at hk ex
  unfold FMv Toward at mv
  unfold Near
  omega

set_option maxHeartbeats 8000000 in
/-- After the step towards the front square, every reply of a lone king that stays on or
above the pawn's rank keeps the race for the opposition, one step shorter. -/
theorem front_reply {m a b c e f p x y X Y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (hf : 3 ≤ f) (h : Front3 (m + 1) a b c e f p) (mv : FMv a b c e p x y) (ap : Apart x y e f)
    (nc : ¬ Capture x y c 3 e f) (dx : Ch x y p 4 m) (st : WeakStep x y c 3 e f X Y)
    (hY' : 2 ≤ m → 3 ≤ Y) : Front3 m x y c X Y p := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, hk, ex, hl, hs, nx, nt, -⟩ := h
  have ex' : ¬ Ch a b p 4 m := ex.resolve_left (by omega)
  clear ex
  obtain ⟨nab, npw⟩ := fmv_near_step hc hp hk ex' mv
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  have n := st.1
  have a7 := st.k7
  have k8 := st.k8
  have k6 := st.k6
  have exr : m = 0 ∨ ¬ Ch x y p 4 (m - 1) := by
    unfold Ch at ex' ⊢
    unfold Near at nab
    omega
  have hlr : ¬ Ch X Y p 6 m := by
    unfold Ch at hl ⊢
    unfold Near at n
    omega
  have sr : ¬ Ch X Y c 3 m ∨ Near x y c 3 ∨ Nr x y c X Y := by
    by_cases g : Ch X Y c 3 m
    · right
      by_cases hn : Near a b c 3
      · exact Or.inl (fmv_near hc hp mv hn)
      right
      rcases hs with hs | hs | ⟨d, kd, ld⟩
      · exfalso
        unfold Ch at hs g
        unfold Near at n
        omega
      · exact absurd hs hn
      · have dm : d ≤ m + 1 := by
          unfold Ch at ld g
          unfold Near at n
          omega
        have tw : Toward a b p 4 x y := by
          rcases mv with ⟨tw, -⟩ | ⟨tw, -, -⟩
          · exact tw
          · exfalso
            unfold Toward at tw
            unfold Near at hn
            omega
        obtain ⟨c1, d2, -⟩ := fmv_closer hp hk ex' kd dm hn D.1.k2 tw
        refine ⟨d - 1, c1, ?_⟩
        unfold Ch at ld ⊢
        unfold Near at n
        omega
    · exact Or.inl g
  have nxr : ¬ Xc x c X p := xc_keep hc u3 u1 u2 u6 u7 hp hf hk ex' hl nx mv ⟨n.2.1, n.1⟩ ⟨n.2.2.2.1, n.2.2.1⟩ a7
  have ntr : ¬ Thr4 x y c p := thr_keep hp hk ex' nt mv
  refine ⟨hp, dx, exr, hlr, sr, nxr, ntr, ?_⟩
  by_cases m1 : m ≤ 1
  · exact Or.inl m1
  right
  have hY := hY' (by omega)
  have xy7 : x ≤ 7 ∧ y ≤ 7 := by
    unfold FMv Toward at mv
    omega
  by_cases m3 : 3 ≤ m
  · exact go_auto u3 xy7.1 xy7.2 n5 n6 hY m3 hp dx (exr.resolve_left (by omega))
      hlr sr a7 k6 k8
  · have hm : m = 2 := by omega
    subst hm
    obtain ⟨u, v, mv2⟩ := fmv_ex x y c X p hc
    have far : X + 3 ≤ p ∨ p + 3 ≤ X := by
      unfold Ch at hl
      unfold Near at n
      omega
    have ex2 : ¬ Ch x y p 4 1 := exr.resolve_left (by omega)
    have npw2 : ¬ (x = c ∧ y = 3) := npw
    obtain ⟨g1, g2, g3⟩ := go_two_core hc u3 xy7.1 xy7.2 hp dx ex2 far ntr npw2 a7 k6 k8 hY mv2
    exact ⟨u, v, mv2, g1, g2, g3⟩

theorem face_mono {i j a b c e f : Nat} (le : i ≤ j) (h : Face i a b c e f) : Face j a b c e f := by
  obtain ⟨y, hf, hy, w1, w2, n, fc⟩ := h
  refine ⟨y, hf, hy, w1, w2, n, ?_⟩
  unfold FC at *
  omega

theorem front_le {m a b c e f p : Nat} (D : DomS a b c 3 e f) (h : Front3 m a b c e f p) :
    m ≤ 7 := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hp, hk, ex, -⟩ := h
  unfold Ch at hk ex
  omega

/-- The outcomes of a position in the front class with the pawn owner to move. -/
theorem front_move {m a b c e f p : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : Front3 m a b c e f p) :
    PushOK3 a b c e f ∨ (∃ q, Key3 1 a b c e f q) ∨ Face 2 a b c e f ∨
      (∃ q n, n ≤ 1 ∧ Key3 n a b c e f q) ∨
      (1 ≤ m ∧ ∃ x y, KingStep a b c 3 e f x y ∧ ¬ Capture x y c 3 e f ∧
        ∀ X Y, WeakStep x y c 3 e f X Y →
          Front3 (m - 1) x y c X Y p ∨ (Y ≤ 2 ∧ ¬ (x = c ∧ y = 4))) := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  by_cases low : f ≤ 2 ∧ ¬ (a = c ∧ b = 4)
  · exact Or.inl (low_push low.1 low.2)
  by_cases m0 : m = 0
  · subst m0
    rcases front0 D hc h with q | q
    · exact Or.inr (Or.inl q)
    · exact Or.inr (Or.inr (Or.inl q))
  by_cases kf : a = c ∧ b = 4
  · obtain ⟨rfl, rfl⟩ := kf
    have k3 := D.1.k3
    have f0 : Front3 0 a 4 a e f a := by
      refine ⟨Or.inr (Or.inl rfl), by unfold Ch; omega, Or.inl rfl, ?_, Or.inl ?_, ?_, ?_,
        Or.inl (by omega)⟩
      · obtain ⟨hp, hk, ex, hl, -⟩ := h
        unfold Ch at hk ex hl ⊢
        rcases ex with ex | ex
        · exact absurd ex m0
        · omega
      · unfold Ch
        omega
      · unfold Xc
        omega
      · unfold Thr4
        omega
    rcases front0 D hc f0 with q | q
    · exact Or.inr (Or.inl q)
    · exact Or.inr (Or.inr (Or.inl q))
  have hf : 3 ≤ f := by
    apply Classical.byContradiction
    intro g
    exact low ⟨by omega, kf⟩
  have hp := h.1
  have hk := h.2.1
  have ex : ¬ Ch a b p 4 (m - 1) := h.2.2.1.resolve_left m0
  have step : ∃ x y, FMv a b c e p x y ∧ Apart x y e f ∧ ¬ Capture x y c 3 e f ∧
      Ch x y p 4 (m - 1) ∨ (m = 1 ∧ ((∃ q n, n ≤ 1 ∧ Key3 n a b c e f q) ∨ Side3 a b c e f)) := by
    rcases h.2.2.2.2.2.2.2 with m1 | go
    · have m1' : m = 1 := by omega
      subst m1'
      obtain ⟨x, y, mv⟩ := fmv_ex a b c e p hc
      by_cases lg : Apart x y e f ∧ ¬ Capture x y c 3 e f
      · refine ⟨x, y, Or.inl ⟨mv, lg.1, lg.2, ?_⟩⟩
        unfold Ch at hk ex ⊢
        unfold FMv Toward at mv
        omega
      · exact ⟨0, 0, Or.inr ⟨rfl, front1_block D hc hf h mv lg⟩⟩
    · obtain ⟨x, y, q⟩ := go
      exact ⟨x, y, Or.inl q⟩
  obtain ⟨x, y, ⟨mv, ap, nc, dx⟩ | ⟨-, q | q⟩⟩ := step
  · have hm : m = (m - 1) + 1 := by omega
    rw [hm] at h
    obtain ⟨nab, npw⟩ := fmv_near_step hc hp (hm ▸ hk) (by rw [hm] at ex; simpa using ex) mv
    have xy7 : x ≤ 7 ∧ y ≤ 7 := by
      unfold FMv Toward at mv
      omega
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, x, y,
      ⟨nab, xy7.1, xy7.2, npw, ap⟩, nc, fun X Y st => ?_⟩)))
    by_cases lowr : Y ≤ 2 ∧ ¬ (x = c ∧ y = 4)
    · exact Or.inr lowr
    · left
      have hY : 2 ≤ m - 1 → 3 ≤ Y := by
        intro m2
        apply Classical.byContradiction
        intro g
        apply lowr
        refine ⟨by omega, ?_⟩
        rintro ⟨rfl, rfl⟩
        unfold Ch at ex
        unfold Near at nab
        omega
      exact front_reply D hc hf h mv ap nc dx st hY
  · exact Or.inr (Or.inr (Or.inr (Or.inl q)))
  · exact Or.inl (side_push D hc q)

end EndgameChess.Rules.KPK.Coord
