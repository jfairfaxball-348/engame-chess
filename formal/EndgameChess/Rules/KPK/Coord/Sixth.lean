import EndgameChess.Rules.KPK.Coord.TopGuard

/-! Draws with a bishop or centre pawn on the sixth rank, strong side to move. The lone
king must be inside the pawn's square. It holds a blockade on the two squares ahead of
the pawn if it gets there no later than the strong king arrives beside or ahead of the
pawn; it holds directly opposite a king beside the pawn; and it wins the race to the pawn
if the strong king is too far to protect it. -/
namespace EndgameChess.Rules.KPK.Coord

/-- Chebyshev distance at most `n`. -/
def Ch (a b x y n : Nat) : Prop := a ≤ x + n ∧ x ≤ a + n ∧ b ≤ y + n ∧ y ≤ b + n

/-- The strong king is more than `n` steps from the squares beside and ahead of the pawn. -/
def Arr (n a b c : Nat) : Prop :=
  ¬ Ch a b (c + 1) 5 n ∧ ¬ Ch a b (c + 1) 6 n ∧ ¬ Ch a b (c - 1) 5 n ∧ ¬ Ch a b (c - 1) 6 n

/-- The lone king is within `n` of a blockade square. -/
def Bl (n c e f : Nat) : Prop := Ch e f c 6 n ∨ Ch e f c 7 n

/-- The lone king is within `n` of a square from which it touches the pawn. -/
def Tc (n c e f : Nat) : Prop :=
  Ch e f (c + 1) 5 n ∨ Ch e f (c - 1) 5 n ∨ Ch e f (c + 1) 4 n ∨ Ch e f (c - 1) 4 n ∨
    Ch e f c 4 n ∨ Ch e f c 6 n

def Key5 (a b c : Nat) : Prop := a ≤ c + 1 ∧ c ≤ a + 1 ∧ (b = 6 ∨ b = 7)

def Beside (a b c : Nat) : Prop := b = 5 ∧ (a = c + 1 ∨ a + 1 = c)

/-- The sixth-rank draw region of files `c`, `d`. -/
def S5 (a b c e f : Nat) : Prop :=
  ¬ Key5 a b c ∧ c + 2 ≥ e ∧ e + 2 ≥ c ∧ 5 ≤ f ∧
    ((Beside a b c ∧ e = a ∧ f = 7) ∨
     (¬ Beside a b c ∧
      ((f = 5 ∧ ((e = c + 1 ∧ a = c + 2) ∨ (e + 1 = c ∧ a + 2 = c)) ∧ b = 7) ∨
       (Bl 0 c e f ∧ Arr 0 a b c) ∨ (Bl 1 c e f ∧ Arr 1 a b c) ∨ (Bl 2 c e f ∧ Arr 2 a b c) ∨
       (f = 5 ∧ ((e = c + 2 ∧ c + 2 ≤ a) ∨ (e + 2 = c ∧ a + 2 ≤ c)) ∧ (b = 3 ∨ b = 7) ∧
         Arr 1 a b c) ∨
       (Tc 0 c e f ∧ ¬ Ch a b c 5 2) ∨ (Tc 1 c e f ∧ ¬ Ch a b c 5 3) ∨
       (Tc 2 c e f ∧ ¬ Ch a b c 5 4))))

/-- The lone king's answer at height 5. -/
def W5 (a b c e f : Nat) : Prop :=
  Capture a b c 5 e f ∨ ∃ x y, WeakStep a b c 5 e f x y ∧ S5 a b c x y

/-- `t` is a file next to the pawn, `o` the other one and `u` two files out beyond `t`. -/
def Sd (c t o u : Nat) : Prop := (t = c + 1 ∧ o + 1 = c ∧ u = c + 2) ∨ (t + 1 = c ∧ o = c + 1 ∧ u + 2 = c)

theorem s5_bl0 {x y c e f : Nat} (b0 : Bl 0 c e f) (r : Arr 0 x y c) (k : ¬ Key5 x y c)
    (nb : ¬ Beside x y c) (h1 : e ≤ c + 2) (h2 : c ≤ e + 2) (h3 : 5 ≤ f) : S5 x y c e f :=
  ⟨k, h1, h2, h3, Or.inr ⟨nb, Or.inr (Or.inl ⟨b0, r⟩)⟩⟩

theorem s5_bl1 {x y c e f : Nat} (b0 : Bl 1 c e f) (r : Arr 1 x y c) (k : ¬ Key5 x y c)
    (nb : ¬ Beside x y c) (h1 : e ≤ c + 2) (h2 : c ≤ e + 2) (h3 : 5 ≤ f) : S5 x y c e f :=
  ⟨k, h1, h2, h3, Or.inr ⟨nb, Or.inr (Or.inr (Or.inl ⟨b0, r⟩))⟩⟩

macro "kk" : tactic => `(tactic| (unfold Key5; omega))
macro "bs" : tactic => `(tactic| (unfold Beside; omega))
macro "ar" : tactic => `(tactic| (unfold Arr Ch; omega))
macro "ws" : tactic => `(tactic| (unfold WeakStep Near Apart Att; omega))

set_option maxHeartbeats 4000000 in
theorem w_front {c x y : Nat} (hc : 2 ≤ c) (hc3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7)
    (s2 : Apart x y c 6) (s3 : ¬ (x = c ∧ y = 5)) : W5 x y c c 6 := by
  unfold Apart at s2
  by_cases near : Near x y c 5
  · unfold Near at near
    exact Or.inr ⟨c, 7, by ws, s5_bl0 (Or.inr (by unfold Ch; omega)) (by ar) (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩
  · exact Or.inl ⟨by unfold Near; omega, near⟩

set_option maxHeartbeats 4000000 in
theorem w_back {c x y : Nat} (hc : 2 ≤ c) (hc3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7)
    (s2 : Apart x y c 7) (s3 : ¬ (x = c ∧ y = 5)) : W5 x y c c 7 := by
  unfold Apart at s2
  by_cases bes : Beside x y c
  · unfold Beside at bes
    refine Or.inr ⟨x, 7, by ws, ?_⟩
    exact ⟨by kk, by omega, by omega, by omega, Or.inl ⟨by unfold Beside; omega, rfl, rfl⟩⟩
  · unfold Beside at bes
    exact Or.inr ⟨c, 6, by ws, s5_bl0 (Or.inl (by unfold Ch; omega)) (by ar) (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
theorem w_t7 {a b c t o u x y : Nat} (hb : b ≤ 7) (hc : 2 ≤ c) (hc3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7) (sd : Sd c t o u)
    (H : Arr 1 a b c ∨ (a = t ∧ b = 5)) (s0 : Near a b x y) (s2 : Apart x y t 7) :
    W5 x y c t 7 := by
  unfold Sd at sd
  unfold Near at s0
  unfold Apart at s2
  unfold Arr Ch at H
  exact Or.inr ⟨c, 7, by ws, s5_bl0 (Or.inr (by unfold Ch; omega)) (by ar) (by kk) (by bs)
    (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
theorem w_u {a b c t o u f x y : Nat} (hc : 2 ≤ c) (hc3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7) (hu : u ≤ 7)
    (sd : Sd c t o u) (hf : f = 6 ∨ f = 7) (H : Arr 2 a b c) (s0 : Near a b x y)
    (s2 : Apart x y u f) : W5 x y c u f := by
  unfold Sd at sd
  unfold Near at s0
  unfold Apart at s2
  unfold Arr Ch at H
  exact Or.inr ⟨t, 7, by ws, s5_bl1 (Or.inr (by unfold Ch; omega)) (by ar) (by kk) (by bs)
    (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
theorem w_u5 {a b c t o u x y : Nat} (hc : 2 ≤ c) (hc3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7) (hu : u ≤ 7)
    (sd : Sd c t o u)
    (H : Arr 2 a b c ∨ (Arr 1 a b c ∧ (u = c + 2 ∧ c + 2 ≤ a ∨ u + 2 = c ∧ a + 2 ≤ c) ∧ (b = 3 ∨ b = 7)))
    (s0 : Near a b x y) (s2 : Apart x y u 5) : W5 x y c u 5 := by
  unfold Sd at sd
  unfold Near at s0
  unfold Apart at s2
  unfold Arr Ch at H
  by_cases top : x = u ∧ y = 7
  · obtain ⟨rfl, rfl⟩ := top
    refine Or.inr ⟨t, 5, by ws, ⟨by kk, by omega, by omega, by omega, Or.inr ⟨by bs, Or.inl ?_⟩⟩⟩
    omega
  · exact Or.inr ⟨t, 5, by ws, s5_bl1 (Or.inl (by unfold Ch; omega)) (by ar) (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
theorem w_t5 {a b c t o u x y : Nat} (hc : 2 ≤ c) (hc3 : c ≤ 3) (hx : x ≤ 7) (hy : y ≤ 7) (sd : Sd c t o u)
    (H : Arr 1 a b c ∨ ¬ Ch a b c 5 2 ∨ (a = u ∧ b = 7)) (s0 : Near a b x y) (s1 : ¬ (x = c ∧ y = 5))
    (s2 : Apart x y t 5) : W5 x y c t 5 := by
  unfold Sd at sd
  unfold Near at s0
  unfold Apart at s2
  unfold Arr Ch at H
  by_cases near : Near x y c 5
  · unfold Near at near
    exact Or.inr ⟨c, 6, by ws, s5_bl0 (Or.inl (by unfold Ch; omega)) (by ar) (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩
  · exact Or.inl ⟨by unfold Near; omega, near⟩

set_option hygiene false in
macro "hy" : tactic => `(tactic| (rintro h; obtain ⟨-, -, -, -, h⟩ := h; unfold Sd at sd; rcases h with ⟨b', e1, f1⟩ | ⟨-, h⟩; (· unfold Beside at b'; unfold Arr Ch; omega); rcases h with A | ⟨B, R⟩ | ⟨B, R⟩ | ⟨B, R⟩ | Sh | ⟨T, F⟩ | ⟨T, F⟩ | ⟨T, F⟩ <;> (try unfold Bl at B) <;> (try unfold Tc at T) <;> (try unfold Arr at R) <;> (try unfold Arr at Sh) <;> (try unfold Ch at *) <;> (try unfold Arr) <;> (try unfold Ch) <;> omega))

set_option maxHeartbeats 4000000 in
theorem h_t7 {a b c t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) :
    S5 a b c t 7 → Arr 1 a b c ∨ (a = t ∧ b = 5) := by hy

set_option maxHeartbeats 4000000 in
theorem h_u {a b c t o u f : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (hf : f = 6 ∨ f = 7) :
    S5 a b c u f → Arr 2 a b c := by hy

set_option maxHeartbeats 4000000 in
theorem h_u5 {a b c t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) :
    S5 a b c u 5 → Arr 2 a b c ∨ (Arr 1 a b c ∧ (u = c + 2 ∧ c + 2 ≤ a ∨ u + 2 = c ∧ a + 2 ≤ c) ∧
      (b = 3 ∨ b = 7)) := by hy

set_option maxHeartbeats 4000000 in
theorem h_t5 {a b c t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) :
    S5 a b c t 5 → Arr 1 a b c ∨ ¬ Ch a b c 5 2 ∨ (a = u ∧ b = 7) := by hy

/-- Every king move inside the region has its answer. -/
theorem s5_king {a b c e f x y : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (h : S5 a b c e f)
    (st : KingStep a b c 5 e f x y) : W5 x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  have k3 := D.1.k3
  have k4 := D.k4
  have s0 := st.1
  have s1 := st.k6
  have s2 : Apart x y e f := st.2.2.2.2
  obtain ⟨-, b1, b2, b3, -⟩ := id h
  have row : f = 5 ∨ f = 6 ∨ f = 7 := by omega
  by_cases mid : e = c
  · subst mid
    rcases row with rfl | rfl | rfl
    · omega
    · exact w_front hc u3 n5 n6 s2 s1
    · exact w_back hc u3 n5 n6 s2 s1
  obtain ⟨t, o, u, sd, ev⟩ : ∃ t o u, Sd c t o u ∧ (e = t ∨ e = u) := by
    by_cases g : c < e
    · exact ⟨c + 1, c - 1, c + 2, Or.inl ⟨rfl, by omega, rfl⟩, by omega⟩
    · exact ⟨c - 1, c + 1, c - 2, Or.inr ⟨by omega, rfl, by omega⟩, by omega⟩
  have sd' := sd
  unfold Sd at sd'
  rcases ev with rfl | rfl <;> rcases row with rfl | rfl | rfl
  · exact w_t5 hc u3 n5 n6 sd (h_t5 hc sd h) s0 s1 s2
  · omega
  · exact w_t7 u2 hc u3 n5 n6 sd (h_t7 hc sd h) s0 s2
  · exact w_u5 hc u3 n5 n6 u6 sd (h_u5 hc sd h) s0 s2
  · exact w_u hc u3 n5 n6 u6 sd (Or.inl rfl) (h_u hc sd (Or.inl rfl) h) s0 s2
  · exact w_u hc u3 n5 n6 u6 sd (Or.inr rfl) (h_u hc sd (Or.inr rfl) h) s0 s2

set_option maxHeartbeats 4000000 in
/-- After a push to the seventh the lone king takes the pawn or reaches the top guard. -/
theorem s5_push {a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (h : S5 a b c e f)
    (fr : Free a b e f c 6) : TW a b c 6 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k3 := D.1.k3
  have k4 := D.k4
  have k1 : Apart a b e f := D.1.k1
  have k2 := D.1.k2
  unfold Free at fr
  obtain ⟨-, b1, b2, b3, -⟩ := id h
  have row : f = 5 ∨ f = 6 ∨ f = 7 := by omega
  by_cases mid : e = c
  · subst mid
    rcases row with rfl | rfl | rfl
    · omega
    · omega
    · refine Or.inl ⟨by unfold Near; omega, ?_⟩
      obtain ⟨-, -, -, -, h⟩ := h
      unfold Apart at k1
      rcases h with ⟨b', e1, _⟩ | ⟨nb, -⟩
      · unfold Beside at b'; omega
      · unfold Beside at nb; unfold Near; omega
  obtain ⟨t, o, u, sd, ev⟩ : ∃ t o u, Sd c t o u ∧ (e = t ∨ e = u) := by
    by_cases g : c < e
    · exact ⟨c + 1, c - 1, c + 2, Or.inl ⟨rfl, by omega, rfl⟩, by omega⟩
    · exact ⟨c - 1, c + 1, c - 2, Or.inr ⟨by omega, rfl, by omega⟩, by omega⟩
  have sd' := sd
  unfold Sd at sd'
  unfold Apart at k1
  rcases ev with rfl | rfl <;> rcases row with rfl | rfl | rfl
  · have H := h_t5 hc sd h
    unfold Arr Ch at H
    exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
  · omega
  · have H := h_t7 hc sd h
    unfold Arr Ch at H
    by_cases at5 : a = e ∧ b = 5
    · obtain ⟨he, rfl⟩ := at5
      refine Or.inr (Or.inr ⟨c, 7, by unfold WeakStep Near Apart Att; omega, by omega, rfl,
        Or.inl ⟨rfl, rfl, by unfold Near; omega, by unfold Near; omega⟩⟩)
    · exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
  all_goals
    have H : Arr 1 a b c := by
      first
        | (have H := h_u5 hc sd h; unfold Arr Ch at H; unfold Arr Ch; omega)
        | (have H := h_u hc sd (Or.inl rfl) h; unfold Arr Ch at H; unfold Arr Ch; omega)
        | (have H := h_u hc sd (Or.inr rfl) h; unfold Arr Ch at H; unfold Arr Ch; omega)
    have far : ¬ Within1 a b o 6 ∧ ¬ Within1 a b o 7 := by
      have G : ¬ Within1 a b o 6 ∧ ¬ Within1 a b o 7 := by
        first
          | (have H := h_u5 hc sd h; unfold Arr Ch at H; unfold Within1; omega)
          | (have H := h_u hc sd (Or.inl rfl) h; unfold Arr Ch at H; unfold Within1; omega)
          | (have H := h_u hc sd (Or.inr rfl) h; unfold Arr Ch at H; unfold Within1; omega)
      exact G
    unfold Arr Ch at H
    refine Or.inr (Or.inr ⟨t, 6, by unfold WeakStep Near Apart Att; omega, by omega, rfl, ?_⟩)
    rcases sd' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have ho : c - 1 = o := by omega
      refine Or.inr (Or.inr ⟨h1, rfl, ?_, ?_⟩)
      · rw [ho]; exact far.1
      · rw [ho]; exact far.2
    · subst h2
      exact Or.inr (Or.inl ⟨h1, rfl, far.1, far.2⟩)

/-- Pawn on the sixth or seventh rank. -/
def sixGuard : Guard where
  S a b c d e f := TS a b c d e f ∨ (d = 5 ∧ 2 ≤ c ∧ S5 a b c e f)
  W a b c d e f := TW a b c d e f ∨ (d = 5 ∧ 2 ≤ c ∧ W5 a b c e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | ⟨rfl, hc, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := topGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r), fun p r t => Or.inl (q3 p r t), q4⟩
    · exact ⟨fun x y st => Or.inr ⟨rfl, hc, s5_king D hc h st⟩, fun fr _ => Or.inl (s5_push D hc h fr),
        fun q => by omega, fun q => by omega⟩
  weak := by
    intro a b c d e f _ h
    rcases h with h | ⟨rfl, hc, h⟩
    · rcases h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inl q⟩)
    · rcases h with q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr ⟨rfl, hc, q⟩⟩)

open EndgameChess.KK in
/-- Bishop or centre pawn on the sixth or seventh rank, a fresh root in the guard with the
pawn owner to move: the lone king holds. -/
theorem fresh_six_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (sat : SD sixGuard σ sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong h fresh turn safe sat

end EndgameChess.Rules.KPK.Coord
