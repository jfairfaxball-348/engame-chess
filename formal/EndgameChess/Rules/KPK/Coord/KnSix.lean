import EndgameChess.Rules.KPK.Coord.KnSeven

/-! Draws with a knight pawn on the sixth rank, strong side to move. The region is that
of `Sixth` read on the knight file, with two more positions: the lone king in the corner
on the pawn's short side, and the king on `c6` or `d8`. There a step next to the corner
stalemates, the advance is met from the promotion square, and anything else lets the
lone king in front of the pawn. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- The sixth-rank draw region of the knight file. -/
def S5n (a b e f : Nat) : Prop :=
  S5 a b 1 e f ∨ (e = 0 ∧ f = 7 ∧ ((a = 2 ∧ b = 5) ∨ (a = 3 ∧ b = 7)))

/-- The lone king's answer: it takes the pawn, is stalemated, or returns to the region. -/
def W5n (a b e f : Nat) : Prop :=
  Capture a b 1 5 e f ∨ (∀ x y, ¬ WeakStep a b 1 5 e f x y) ∨
    ∃ x y, WeakStep a b 1 5 e f x y ∧ S5n a b x y

theorem w5n_of {a b e f : Nat} (h : W5 a b 1 e f) : W5n a b e f := by
  rcases h with h | ⟨x, y, st, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨x, y, st, Or.inl h⟩)

set_option maxHeartbeats 4000000 in
/-- Lone king in the corner: what the region says about the king. -/
theorem hl7 {a b : Nat} : S5 a b 1 0 7 → Arr 1 a b 1 ∨ (a = 0 ∧ b = 5) := by
  rintro h
  obtain ⟨-, -, -, -, h⟩ := h
  rcases h with ⟨b', e1, f1⟩ | ⟨-, h⟩
  · unfold Beside at b'
    unfold Arr Ch
    omega
  rcases h with A | ⟨B, R⟩ | ⟨B, R⟩ | ⟨B, R⟩ | Sh | ⟨T, F⟩ | ⟨T, F⟩ | ⟨T, F⟩ <;>
    (try unfold Bl at B) <;> (try unfold Tc at T) <;> (try unfold Arr at R) <;>
    (try unfold Arr at Sh) <;> (try unfold Ch at *) <;> (try unfold Arr) <;>
    (try unfold Ch) <;> omega

set_option maxHeartbeats 4000000 in
/-- Lone king on the rook file beside the pawn. -/
theorem hl5 {a b : Nat} : S5 a b 1 0 5 → Arr 1 a b 1 ∨ ¬ Ch a b 1 5 2 := by
  rintro h
  obtain ⟨-, -, -, -, h⟩ := h
  rcases h with ⟨b', e1, f1⟩ | ⟨-, h⟩
  · omega
  rcases h with A | ⟨B, R⟩ | ⟨B, R⟩ | ⟨B, R⟩ | Sh | ⟨T, F⟩ | ⟨T, F⟩ | ⟨T, F⟩ <;>
    (try unfold Bl at B) <;> (try unfold Tc at T) <;> (try unfold Arr at R) <;>
    (try unfold Arr at Sh) <;> (try unfold Ch at *) <;> (try unfold Arr) <;>
    (try unfold Ch) <;> omega

set_option maxHeartbeats 4000000 in
/-- From the corner the lone king steps to the promotion square. -/
theorem wl7 {a b x y : Nat} (hb : b ≤ 7) (hx : x ≤ 7) (hy : y ≤ 7)
    (H : Arr 1 a b 1 ∨ (a = 0 ∧ b = 5)) (s0 : Near a b x y) (s2 : Apart x y 0 7) :
    W5 x y 1 0 7 := by
  unfold Near at s0
  unfold Apart at s2
  unfold Arr Ch at H
  exact Or.inr ⟨1, 7, by ws, s5_bl0 (Or.inr (by unfold Ch; omega)) (by ar) (by kk) (by bs)
    (by omega) (by omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- From beside the pawn on the rook file it takes the pawn or steps in front of it. -/
theorem wl5 {a b x y : Nat} (hx : x ≤ 7) (hy : y ≤ 7) (H : Arr 1 a b 1 ∨ ¬ Ch a b 1 5 2)
    (s0 : Near a b x y) (s1 : ¬ (x = 1 ∧ y = 5)) (s2 : Apart x y 0 5) : W5 x y 1 0 5 := by
  unfold Near at s0
  unfold Apart at s2
  unfold Arr Ch at H
  by_cases near : Near x y 1 5
  · unfold Near at near
    exact Or.inr ⟨1, 6, by ws, s5_bl0 (Or.inl (by unfold Ch; omega)) (by ar) (by kk) (by bs)
      (by omega) (by omega) (by omega)⟩
  · exact Or.inl ⟨by unfold Near; omega, near⟩

set_option maxHeartbeats 4000000 in
/-- The corner draws: a step next to the corner stalemates, and any other step lets the
lone king in front of the pawn. -/
theorem wn_corner {a b x y : Nat} (hx : x ≤ 7) (hy : y ≤ 7)
    (pos : (a = 2 ∧ b = 5) ∨ (a = 3 ∧ b = 7)) (s0 : Near a b x y) (s1 : ¬ (x = 1 ∧ y = 5))
    (s2 : Apart x y 0 7) : W5n x y 0 7 := by
  unfold Near at s0
  unfold Apart at s2
  by_cases g : x = 2 ∧ 6 ≤ y
  · refine Or.inr (Or.inl fun p q st => ?_)
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
    have k5 := st.k5
    have k7 := st.k7
    have k8 := st.k8
    omega
  · exact Or.inr (Or.inr ⟨1, 6, by ws, Or.inl (s5_bl0 (Or.inl (by unfold Ch; omega)) (by ar)
      (by kk) (by bs) (by omega) (by omega) (by omega))⟩)

/-- Every king move inside the region has its answer. -/
theorem s5n_king {a b e f x y : Nat} (D : DomS a b 1 5 e f) (h : S5n a b e f)
    (st : KingStep a b 1 5 e f x y) : W5n x y e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
  have k3 := D.1.k3
  have k4 := D.k4
  have s0 := st.1
  have s1 := st.k6
  have s2 : Apart x y e f := st.2.2.2.2
  have hc1 : 1 ≤ 1 := Nat.le_refl 1
  rcases h with h | ⟨rfl, rfl, pos⟩
  rotate_left
  · exact wn_corner n5 n6 pos s0 s1 s2
  obtain ⟨-, b1, b2, b3, -⟩ := id h
  have row : f = 5 ∨ f = 6 ∨ f = 7 := by omega
  have sd : Sd 1 2 0 3 := Or.inl ⟨rfl, rfl, rfl⟩
  have ecase : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  apply w5n_of
  rcases ecase with rfl | rfl | rfl | rfl <;> rcases row with rfl | rfl | rfl
  · exact wl5 n5 n6 (hl5 h) s0 s1 s2
  · omega
  · exact wl7 u2 n5 n6 (hl7 h) s0 s2
  · omega
  · exact w_front hc1 (by omega) n5 n6 s2 s1
  · exact w_back hc1 (by omega) n5 n6 s2 s1
  · exact w_t5 hc1 (by omega) n5 n6 sd (h_t5 hc1 sd h) s0 s1 s2
  · omega
  · exact w_t7 u2 hc1 (by omega) n5 n6 sd (h_t7 hc1 sd h) s0 s2
  · exact w_u5 hc1 (by omega) n5 n6 (by omega) sd (h_u5 hc1 sd h) s0 s2
  · exact w_u hc1 (by omega) n5 n6 (by omega) sd (Or.inl rfl) (h_u hc1 sd (Or.inl rfl) h) s0 s2
  · exact w_u hc1 (by omega) n5 n6 (by omega) sd (Or.inr rfl) (h_u hc1 sd (Or.inr rfl) h) s0 s2

set_option maxHeartbeats 4000000 in
/-- After a push to the seventh the lone king takes the pawn or reaches the top guard. -/
theorem s5n_push {a b e f : Nat} (D : DomS a b 1 5 e f) (h : S5n a b e f)
    (fr : Free a b e f 1 6) : TW a b 1 6 e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k3 := D.1.k3
  have k4 := D.k4
  have k1 : Apart a b e f := D.1.k1
  have k2 := D.1.k2
  have hc1 : 1 ≤ 1 := Nat.le_refl 1
  unfold Free at fr
  unfold Apart at k1
  rcases h with h | ⟨rfl, rfl, pos⟩
  rotate_left
  · rcases pos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨1, 7, by unfold WeakStep Near Apart Att; omega, by omega, rfl,
        Or.inl ⟨rfl, rfl, by unfold Near; omega, by unfold Near; omega⟩⟩)
    · exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
  obtain ⟨-, b1, b2, b3, -⟩ := id h
  have row : f = 5 ∨ f = 6 ∨ f = 7 := by omega
  have sd : Sd 1 2 0 3 := Or.inl ⟨rfl, rfl, rfl⟩
  have ecase : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases ecase with rfl | rfl | rfl | rfl <;> rcases row with rfl | rfl | rfl
  · have H := hl5 h
    unfold Arr Ch at H
    exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
  · omega
  · have H := hl7 h
    unfold Arr Ch at H
    by_cases at5 : a = 0 ∧ b = 5
    · obtain ⟨rfl, rfl⟩ := at5
      exact Or.inr (Or.inr ⟨1, 7, by unfold WeakStep Near Apart Att; omega, by omega, rfl,
        Or.inl ⟨rfl, rfl, by unfold Near; omega, by unfold Near; omega⟩⟩)
    · exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
  · omega
  · omega
  · refine Or.inl ⟨by unfold Near; omega, ?_⟩
    obtain ⟨-, -, -, -, h⟩ := h
    rcases h with ⟨b', e1, _⟩ | ⟨nb, -⟩
    · unfold Beside at b'; omega
    · unfold Beside at nb; unfold Near; omega
  · have H := h_t5 hc1 sd h
    unfold Arr Ch at H
    exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
  · omega
  · have H := h_t7 hc1 sd h
    unfold Arr Ch at H
    by_cases at5 : a = 2 ∧ b = 5
    · obtain ⟨rfl, rfl⟩ := at5
      exact Or.inr (Or.inr ⟨1, 7, by unfold WeakStep Near Apart Att; omega, by omega, rfl,
        Or.inl ⟨rfl, rfl, by unfold Near; omega, by unfold Near; omega⟩⟩)
    · exact Or.inl ⟨by unfold Near; omega, by unfold Near; omega⟩
  all_goals
    have H : Arr 1 a b 1 ∧ ¬ Within1 a b 0 6 ∧ ¬ Within1 a b 0 7 := by
      first
        | (have H := h_u5 hc1 sd h; unfold Arr Ch at H; unfold Arr Ch Within1; omega)
        | (have H := h_u hc1 sd (Or.inl rfl) h; unfold Arr Ch at H; unfold Arr Ch Within1; omega)
        | (have H := h_u hc1 sd (Or.inr rfl) h; unfold Arr Ch at H; unfold Arr Ch Within1; omega)
    obtain ⟨H, far1, far2⟩ := H
    unfold Arr Ch at H
    exact Or.inr (Or.inr ⟨2, 6, by unfold WeakStep Near Apart Att; omega, by omega, rfl,
      Or.inr (Or.inr ⟨rfl, rfl, far1, far2⟩)⟩)

/-- Knight pawn on the sixth or seventh rank. -/
def knSixGuard : Guard where
  S a b c d e f := TS a b c d e f ∨ (d = 5 ∧ c = 1 ∧ S5n a b e f)
  W a b c d e f := TW a b c d e f ∨ (d = 5 ∧ c = 1 ∧ W5n a b e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | ⟨rfl, rfl, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := topGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r),
        fun p r t => Or.inl (q3 p r t), q4⟩
    · exact ⟨fun x y st => Or.inr ⟨rfl, rfl, s5n_king D h st⟩,
        fun fr _ => Or.inl (s5n_push D h fr), fun q => by omega, fun q => by omega⟩
  weak := by
    intro a b c d e f _ h
    rcases h with h | ⟨rfl, rfl, h⟩
    · rcases h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inl q⟩)
    · rcases h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr ⟨rfl, rfl, q⟩⟩)

/-- Knight pawn on the sixth or seventh rank, a fresh root in the guard with the pawn
owner to move: the lone king holds. -/
theorem fresh_kn_six_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (sat : SD knSixGuard σ sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong h fresh turn safe sat

end EndgameChess.Rules.KPK.Coord
