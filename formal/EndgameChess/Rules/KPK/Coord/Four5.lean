import EndgameChess.Rules.KPK.Coord.Four4

/-! Fourth rank: the opposition. The key squares of a pawn on `(c,3)` are `(c-1,5)`,
`(c,5)` and `(c+1,5)`. The lone king keeps the king off them by guarding them, and the
square `(c,6)` guards all three. Two clauses follow. In distant opposition (`Opd`) the
kings stand on one file at most four files from the pawn, the lone king on rank 7 or 8 and
the king on rank 5 or lower, with an odd number of squares between them. The lone king
answers each king step on the same file and restores the parity between ranks 7 and 8.
On the guard square (`GSq`) the lone king stands on `(c,6)` with the king two files out on
rank 4, 5 or 6. -/
namespace EndgameChess.Rules.KPK.Coord

/-- Distant opposition on a file at most four files from the pawn. -/
def Opd (a b c e f : Nat) : Prop :=
  e = a ∧ ((f = 6 ∧ (b = 0 ∨ b = 2 ∨ b = 4)) ∨ (f = 7 ∧ (b = 1 ∨ b = 3))) ∧
    a ≤ c + 4 ∧ c ≤ a + 4

/-- The lone king on the guard square, the king two files out. -/
def GSq (a b c e f : Nat) : Prop := e = c ∧ f = 6 ∧ (a = c + 2 ∨ a + 2 = c) ∧ 3 ≤ b ∧ b ≤ 5

/-- The explicit part with the opposition. -/
def C4 (a b c e f : Nat) : Prop := C3 a b c e f ∨ Opd a b c e f ∨ GSq a b c e f

/-- The lone king's answer into it. -/
def WC4 (a b c e f : Nat) : Prop :=
  Capture a b c 3 e f ∨ ∃ x y, WeakStep a b c 3 e f x y ∧ C4 a b c x y

theorem wc4_of_wc3 {a b c e f : Nat} (h : WC3 a b c e f) : WC4 a b c e f := by
  rcases h with q | ⟨x, y, st, q⟩
  · exact Or.inl q
  · exact Or.inr ⟨x, y, st, Or.inl q⟩

/-! ## Distant opposition -/

set_option maxHeartbeats 8000000 in
/-- Leaving the four-file window on the far side, the king lets the lone king step towards
the pawn into the lifted region. -/
theorem opd_out {c y f : Nat} (hc : 1 ≤ c) (h2 : c ≤ 2) (hy : y ≤ 4) (hf : f = 6 ∨ f = 7) :
    S3 (c + 5) y c (c + 3) (f - 1) := by
  rcases hf with rfl | rfl
  · exact ⟨by omega, y + 1, Or.inl ⟨by omega, rfl⟩, by unfold Apart; omega,
      by unfold K4; omega, by unfold Sq4; omega, Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl (by m4d))⟩⟩
  · exact ⟨by omega, y + 1, Or.inl ⟨by omega, rfl⟩, by unfold Apart; omega,
      by unfold K4; omega, by unfold Sq4; omega, Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl (by m4d))⟩⟩

set_option maxHeartbeats 8000000 in
/-- In distant opposition the lone king mirrors every king step. -/
theorem opd_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : Opd a b c e f)
    (st : KingStep a b c 3 e f x y) : WC4 x y c e f := by
  have h3 := D.bounds.2.2.1
  obtain ⟨he, par, w1, w2⟩ := h
  subst e
  have s0 := st
  unfold KingStep Near Apart at s0
  have hy : y ≤ 4 := by omega
  have yc : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega
  by_cases win : x ≤ c + 4
  · have g : ∃ g, (g = 6 ∧ (y = 0 ∨ y = 2 ∨ y = 4)) ∨ (g = 7 ∧ (y = 1 ∨ y = 3)) := by
      rcases yc with h | h | h | h | h
      · exact ⟨6, Or.inl ⟨rfl, Or.inl h⟩⟩
      · exact ⟨7, Or.inr ⟨rfl, Or.inl h⟩⟩
      · exact ⟨6, Or.inl ⟨rfl, Or.inr (Or.inl h)⟩⟩
      · exact ⟨7, Or.inr ⟨rfl, Or.inr h⟩⟩
      · exact ⟨6, Or.inl ⟨rfl, Or.inr (Or.inr h)⟩⟩
    obtain ⟨g, hg⟩ := g
    refine Or.inr ⟨x, g, ?_, Or.inr (Or.inl ⟨rfl, hg, win, by omega⟩)⟩
    unfold WeakStep Near Apart Att
    omega
  · have hx : x = c + 5 := by omega
    subst hx
    have ha : a = c + 4 := by omega
    subst ha
    refine Or.inr ⟨c + 3, f - 1, ?_, Or.inl (Or.inl (opd_out hc (by omega) hy (by omega)))⟩
    unfold WeakStep Near Apart Att
    omega

theorem ocr_toward {a b c u v : Nat} (hb : b ≤ 4) (w1 : a ≤ c + 4) (w2 : c ≤ a + 4)
    (ne : a ≠ c) (tu : (a < c ∧ u = a + 1) ∨ (c < a ∧ u + 1 = a)) (hv : v = 6) :
    Ocr a b c u v := by
  unfold Ocr
  by_cases g : c < u
  · left
    omega
  · right
    intro n kr
    unfold Ch at *
    omega

theorem ocl_toward {a b c u v : Nat} (hb : b ≤ 4) (w1 : a ≤ c + 4) (w2 : c ≤ a + 4)
    (ne : a ≠ c) (tu : (a < c ∧ u = a + 1) ∨ (c < a ∧ u + 1 = a)) (hv : v = 6) :
    Ocl a b c u v := by
  unfold Ocl
  by_cases g : u < c
  · left
    omega
  · right
    intro n kr
    unfold Ch at *
    omega

set_option maxHeartbeats 8000000 in
/-- After a push from distant opposition the lone king steps towards the square two ahead
of the pawn, or in front of the pawn when it is already there. -/
theorem opd_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : Opd a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  have h3 := D.bounds.2.2.1
  have h7 := D.bounds.1
  obtain ⟨he, par, w1, w2⟩ := h
  subst e
  have hb : b ≤ 4 := by omega
  have hf : f = 6 ∨ f = 7 := by omega
  unfold Free at fr
  have kx : ¬ K4 a b c := by unfold K4; omega
  by_cases bes : B4 a b c
  · have bes' := bes
    unfold B4 at bes'
    have f6 : f = 6 := by omega
    subst f6
    exact Or.inr ⟨c, 6, by unfold WeakStep Near Apart Att; omega, kx, by unfold Sq4; omega,
      Or.inl ⟨bes, rfl, Or.inr rfl⟩⟩
  have bx := bes
  by_cases mid : a = c
  · rcases hf with rfl | rfl
    · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega,
        s4_center hc rfl (Or.inl rfl) kx bx⟩
    · exact Or.inr ⟨c, 6, by unfold WeakStep Near Apart Att; omega,
        s4_center hc rfl (Or.inr rfl) kx bx⟩
  · have tu : ∃ u, (a < c ∧ u = a + 1) ∨ (c < a ∧ u + 1 = a) := by
      by_cases g : a < c
      · exact ⟨a + 1, Or.inl ⟨g, rfl⟩⟩
      · exact ⟨a - 1, Or.inr ⟨by omega, by omega⟩⟩
    obtain ⟨u, tu⟩ := tu
    refine Or.inr ⟨u, 6, ?_, kx, by unfold Sq4; omega, Or.inr ⟨bx, Or.inr (Or.inl
      ⟨⟨?_, ?_, ?_, ?_⟩, ocr_toward hb w1 w2 mid tu rfl, ocl_toward hb w1 w2 mid tu rfl⟩)⟩⟩
    · unfold WeakStep Near Apart Att
      omega
    all_goals race2

/-! ## The guard square -/

set_option maxHeartbeats 8000000 in
theorem gsq_3_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (st : KingStep a 3 c 3 c 6 x y) : WC4 x y c c 6 := by
  have cs : (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x + 1 = a ∧ y = 4) ∨
      (x = a ∧ y = 2) ∨
      (x = a ∧ y = 4) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a + 1 ∧ y = 4) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inr (Or.inl (by unfold Opd; omega))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩

set_option maxHeartbeats 8000000 in
theorem gsq_3_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (fr : Free a 3 c 6 c 4) : W4 a 3 c c 6 := by
  unfold Free at fr
  exact Or.inr ⟨c - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem gsq_4_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (st : KingStep a 4 c 3 c 6 x y) : WC4 x y c c 6 := by
  have cs : (x + 1 = a ∧ y = 3) ∨
      (x + 1 = a ∧ y = 4) ∨
      (x = a ∧ y = 3) ∨
      (x = a ∧ y = 5) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a + 1 ∧ y = 4) ∨
      (x = a + 1 ∧ y = 5) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inr (Or.inl (by unfold Opd; omega))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩

set_option maxHeartbeats 8000000 in
theorem gsq_4_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (fr : Free a 4 c 6 c 4) : W4 a 4 c c 6 := by
  unfold Free at fr
  exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem gsq_5_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (st : KingStep a 5 c 3 c 6 x y) : WC4 x y c c 6 := by
  have cs : (x + 1 = a ∧ y = 4) ∨
      (x = a ∧ y = 4) ∨
      (x = a ∧ y = 6) ∨
      (x = a + 1 ∧ y = 4) ∨
      (x = a + 1 ∧ y = 5) ∨
      (x = a + 1 ∧ y = 6) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨c + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inr (Or.inl (by unfold Opd; omega))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩

set_option maxHeartbeats 8000000 in
theorem gsq_5_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (fr : Free a 5 c 6 c 4) : W4 a 5 c c 6 := by
  unfold Free at fr
  exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem gsq_3_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (st : KingStep a 3 c 3 c 6 x y) : WC4 x y c c 6 := by
  have cs : (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a + 1 ∧ y = 4) ∨
      (x = a ∧ y = 2) ∨
      (x = a ∧ y = 4) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x + 1 = a ∧ y = 4) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inr (Or.inl (by unfold Opd; omega))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩

set_option maxHeartbeats 8000000 in
theorem gsq_3_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (fr : Free a 3 c 6 c 4) : W4 a 3 c c 6 := by
  unfold Free at fr
  exact Or.inr ⟨c + 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem gsq_4_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (st : KingStep a 4 c 3 c 6 x y) : WC4 x y c c 6 := by
  have cs : (x = a + 1 ∧ y = 3) ∨
      (x = a + 1 ∧ y = 4) ∨
      (x = a ∧ y = 3) ∨
      (x = a ∧ y = 5) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x + 1 = a ∧ y = 4) ∨
      (x + 1 = a ∧ y = 5) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inr (Or.inl (by unfold Opd; omega))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩

set_option maxHeartbeats 8000000 in
theorem gsq_4_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (fr : Free a 4 c 6 c 4) : W4 a 4 c c 6 := by
  unfold Free at fr
  exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem gsq_5_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (st : KingStep a 5 c 3 c 6 x y) : WC4 x y c c 6 := by
  have cs : (x = a + 1 ∧ y = 4) ∨
      (x = a ∧ y = 4) ∨
      (x = a ∧ y = 6) ∨
      (x + 1 = a ∧ y = 4) ∨
      (x + 1 = a ∧ y = 5) ∨
      (x + 1 = a ∧ y = 6) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨c - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inr (Or.inl (by unfold Opd; omega))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩
  · exact Or.inr ⟨c + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (by s3t))⟩

set_option maxHeartbeats 8000000 in
theorem gsq_5_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (fr : Free a 5 c 6 c 4) : W4 a 5 c c 6 := by
  unfold Free at fr
  exact Or.inr ⟨c, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
/-- Every king step from the guard square is answered into the explicit part. -/
theorem gsq_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : GSq a b c e f)
    (st : KingStep a b c 3 e f x y) : WC4 x y c e f := by
  have h3 := D.bounds.2.2.1
  obtain ⟨rfl, rfl, side, hb1, hb2⟩ := h
  have hb : b = 3 ∨ b = 4 ∨ b = 5 := by omega
  rcases side with s | s <;> rcases hb with rfl | rfl | rfl
  · exact gsq_3_r_k hc h3 (by omega) st
  · exact gsq_4_r_k hc h3 (by omega) st
  · exact gsq_5_r_k hc h3 (by omega) st
  · exact gsq_3_l_k hc h3 (by omega) st
  · exact gsq_4_l_k hc h3 (by omega) st
  · exact gsq_5_l_k hc h3 (by omega) st

set_option maxHeartbeats 8000000 in
theorem gsq_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : GSq a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  have h3 := D.bounds.2.2.1
  obtain ⟨rfl, rfl, side, hb1, hb2⟩ := h
  have hb : b = 3 ∨ b = 4 ∨ b = 5 := by omega
  rcases side with s | s <;> rcases hb with rfl | rfl | rfl
  · exact gsq_3_r_p hc h3 (by omega) fr
  · exact gsq_4_r_p hc h3 (by omega) fr
  · exact gsq_5_r_p hc h3 (by omega) fr
  · exact gsq_3_l_p hc h3 (by omega) fr
  · exact gsq_4_l_p hc h3 (by omega) fr
  · exact gsq_5_l_p hc h3 (by omega) fr

/-! ## The region with the opposition -/

/-- The explicit part is closed. -/
theorem c4_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : C4 a b c e f)
    (st : KingStep a b c 3 e f x y) : WC4 x y c e f := by
  rcases h with h | h | h
  · exact wc4_of_wc3 (c3_king D hc h st)
  · exact opd_king D hc h st
  · exact gsq_king D hc h st

theorem c4_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : C4 a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  rcases h with h | h | h
  · exact c3_push D hc h fr
  · exact opd_push D hc h fr
  · exact gsq_push D hc h fr

/-- A tempo position answered into the explicit part with the opposition. -/
def T4 (a b c e f : Nat) : Prop :=
  (f = 7 ∨ e = c + 4 ∨ e + 4 = c ∨ b = 7) ∧
    (∀ x y, KingStep a b c 3 e f x y → WC4 x y c e f) ∧ (Free a b e f c 4 → W4 a b c e f)

/-- The fourth-rank draw region with the opposition. -/
def R4 (a b c e f : Nat) : Prop := C4 a b c e f ∨ T4 a b c e f

def WR4 (a b c e f : Nat) : Prop :=
  Capture a b c 3 e f ∨ ∃ x y, WeakStep a b c 3 e f x y ∧ R4 a b c x y

theorem wr4_of_wc4 {a b c e f : Nat} (h : WC4 a b c e f) : WR4 a b c e f := by
  rcases h with q | ⟨x, y, st, q⟩
  · exact Or.inl q
  · exact Or.inr ⟨x, y, st, Or.inl q⟩

theorem r4_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : R4 a b c e f)
    (st : KingStep a b c 3 e f x y) : WR4 x y c e f := by
  rcases h with h | ⟨-, k, -⟩
  · exact wr4_of_wc4 (c4_king D hc h st)
  · exact wr4_of_wc4 (k x y st)

theorem r4_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : R4 a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  rcases h with h | ⟨-, -, p⟩
  · exact c4_push D hc h fr
  · exact p fr

/-- Pawn on the fourth to seventh rank, any non-rook file, with the opposition region. -/
def fourGuardO : Guard where
  S a b c d e f := fiveGuard.S a b c d e f ∨ knFiveGuard.S a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ R4 a b c e f)
  W a b c d e f := fiveGuard.W a b c d e f ∨ knFiveGuard.W a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ WR4 a b c e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | h | ⟨rfl, hc, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := fiveGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r),
        fun p r t => Or.inl (q3 p r t), q4⟩
    · obtain ⟨q1, q2, q3, q4⟩ := knFiveGuard.strong D h
      exact ⟨fun x y s => Or.inr (Or.inl (q1 x y s)), fun p r => Or.inr (Or.inl (q2 p r)),
        fun p r t => Or.inr (Or.inl (q3 p r t)), q4⟩
    · refine ⟨fun x y st => Or.inr (Or.inr ⟨rfl, hc, r4_king D hc h st⟩), fun fr _ => ?_,
        fun q => by omega, fun q => by omega⟩
      have w := r4_push D hc h fr
      by_cases c1 : c = 1
      · subst c1
        exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl, w⟩))
      · exact Or.inl (Or.inr ⟨rfl, by omega, w⟩)
  weak := by
    intro a b c d e f D h
    rcases h with h | h | ⟨rfl, hc, h⟩
    · rcases fiveGuard.weak D h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inl q⟩)
    · rcases knFiveGuard.weak D h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr (Or.inl q)⟩)
    · rcases h with q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr (Or.inr ⟨rfl, hc, q⟩)⟩)

open EndgameChess.KK in
/-- Non-rook pawn on the fourth rank, pawn owner to move, root in the opposition region:
the lone king holds, and no forced mate exists at any length. -/
theorem fresh_four_hold_o {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (sat : R4 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong (G := fourGuardO) h fresh turn safe (Or.inr (Or.inr ⟨rank, file, sat⟩))

open EndgameChess.KK in
/-- Non-rook pawn on the fourth rank, lone king to move: it holds if it takes the pawn or
steps into the opposition region. -/
theorem fresh_four_weak_hold_o {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (w : WR4 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_weak (G := fourGuardO) h fresh turn (Or.inr (Or.inr ⟨rank, file, w⟩))

end EndgameChess.Rules.KPK.Coord
