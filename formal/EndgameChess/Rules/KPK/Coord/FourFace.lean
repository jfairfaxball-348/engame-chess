import EndgameChess.Rules.KPK.Coord.FourKey

/-! Fourth rank, the winning side: face-offs. The king steps onto the lone king's file, at
most four files from the pawn, two ranks below it: on the fifth rank against a lone king
on the seventh, or on the sixth rank against a lone king on the eighth. The lone king must
step aside. If it steps away from the pawn's file, the king wins the race to the nearest
key square on its side; if it steps towards the pawn's file or straight up, the king faces
it again, nearer to the pawn or one rank higher. A face-off `k` files from the pawn costs
`2 + 2k` from the fifth rank and `1 + 2k` from the sixth. -/
namespace EndgameChess.Rules.KPK.Coord

/-- The cost of a face-off from rank `y` (fifth or sixth) on file `x` is at most `j`. -/
def FC (y x c j : Nat) : Prop :=
  (y = 4 ∧ 2 + 2 * (x - c) + 2 * (c - x) ≤ j) ∨ (y = 5 ∧ 1 + 2 * (x - c) + 2 * (c - x) ≤ j)

/-- Pawn owner to move: the king can step onto the lone king's file two ranks below it,
at a cost of at most `j`. -/
def Face (j a b c e f : Nat) : Prop :=
  ∃ y, f = y + 2 ∧ (y = 4 ∨ y = 5) ∧ e ≤ c + 4 ∧ c ≤ e + 4 ∧ Near a b e y ∧ FC y e c j

/-- Lone king to move, two ranks above the king on its file, with phase `i` left. -/
def FaceW (i x y c e f : Nat) : Prop :=
  e = x ∧ f = y + 2 ∧ (y = 4 ∨ y = 5) ∧ x ≤ c + 4 ∧ c ≤ x + 4 ∧ FC y x c (i + 1)

theorem face_step {j a b c e f : Nat} (D : DomS a b c 3 e f) (h : Face j a b c e f) :
    ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c 3 e f x y ∧ FaceW i x y c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨y, rfl, hy, w1, w2, n, fc⟩ := h
  have hj : 1 ≤ j := by
    unfold FC at fc
    omega
  refine ⟨j - 1, by omega, e, y, ⟨n, u6, by omega, by omega, by unfold Apart; omega⟩,
    rfl, rfl, hy, w1, w2, ?_⟩
  unfold FC at fc ⊢
  omega

theorem facew_keep {i x y c e f : Nat} (h : FaceW i x y c e f) : ¬ Capture x y c 3 e f := by
  obtain ⟨-, rfl, hy, -⟩ := h
  unfold Capture Near
  omega

set_option maxHeartbeats 4000000 in
/-- The king in front of the pawn: every reply loses the race to a key square. -/
theorem facew_front {i y c X Y : Nat} (hc : 1 ≤ c) (hy : y = 4 ∨ y = 5)
    (fc : FC y c c (i + 1)) (n : Near c (y + 2) X Y) (ap : Apart c y X Y) :
    ∃ p m, m ≤ i ∧ Key3 m c y c X Y p := by
  unfold FC at fc
  unfold Near at n
  unfold Apart at ap
  rcases hy with rfl | rfl
  · by_cases g : X + 1 = c
    · exact ⟨c + 1, 1, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
        Or.inl (by unfold Ch; omega)⟩
    by_cases g2 : X = c + 1
    · exact ⟨c - 1, 1, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
        Or.inl (by unfold Ch; omega)⟩
    · exact ⟨c, 1, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
        Or.inl (by unfold Ch; omega)⟩
  · exact ⟨c, 0, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
      Or.inl (by unfold Ch; omega)⟩

set_option maxHeartbeats 4000000 in
/-- The king right of the pawn: a step away is met by the race, any other step by a new
face-off. -/
theorem facew_right {i x y c X Y : Nat} (hy : y = 4 ∨ y = 5) (lt : c < x)
    (w1 : x ≤ c + 4) (fc : FC y x c (i + 1)) (n : Near x (y + 2) X Y) (ap : Apart x y X Y)
    (hY : Y ≤ 7) :
    (∃ p m, m ≤ i ∧ Key3 m x y c X Y p) ∨ Face i x y c X Y := by
  unfold FC at fc
  unfold Near at n
  unfold Apart at ap
  by_cases away : X = x + 1
  · left
    by_cases k1 : x = c + 1
    · rcases hy with rfl | rfl
      · exact ⟨c, 1, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
          Or.inl (by unfold Ch; omega)⟩
      · exact ⟨x, 0, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
          Or.inl (by unfold Ch; omega)⟩
    · exact ⟨c + 1, x - c - 1, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
        Or.inl (by unfold Ch; omega)⟩
  · right
    refine ⟨Y - 2, by omega, by omega, by omega, by omega, by unfold Near; omega, ?_⟩
    unfold FC
    omega

set_option maxHeartbeats 4000000 in
/-- The same left of the pawn. -/
theorem facew_left {i x y c X Y : Nat} (hc : 1 ≤ c) (hy : y = 4 ∨ y = 5) (lt : x < c)
    (w2 : c ≤ x + 4) (fc : FC y x c (i + 1)) (n : Near x (y + 2) X Y) (ap : Apart x y X Y)
    (hY : Y ≤ 7) :
    (∃ p m, m ≤ i ∧ Key3 m x y c X Y p) ∨ Face i x y c X Y := by
  unfold FC at fc
  unfold Near at n
  unfold Apart at ap
  by_cases away : X + 1 = x
  · left
    by_cases k1 : x + 1 = c
    · rcases hy with rfl | rfl
      · exact ⟨c, 1, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
          Or.inl (by unfold Ch; omega)⟩
      · exact ⟨x, 0, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
          Or.inl (by unfold Ch; omega)⟩
    · exact ⟨c - 1, c - x - 1, by omega, by omega, by unfold Ch; omega, by unfold Ch; omega,
        Or.inl (by unfold Ch; omega)⟩
  · right
    refine ⟨Y - 2, by omega, by omega, by omega, by omega, by unfold Near; omega, ?_⟩
    unfold FC
    omega

/-- Every reply to a face-off is a won race or a cheaper face-off. -/
theorem facew_reply {i x y c e f X Y : Nat} (hc : 1 ≤ c) (h : FaceW i x y c e f)
    (st : WeakStep x y c 3 e f X Y) :
    (∃ p m, m ≤ i ∧ Key3 m x y c X Y p) ∨ Face i x y c X Y := by
  obtain ⟨rfl, rfl, hy, w1, w2, fc⟩ := h
  have n := st.1
  have ap := st.k7
  have hY := st.2.2.1
  rcases Nat.lt_trichotomy e c with lt | h0 | gt
  · exact facew_left hc hy lt w2 fc n ap hY
  · subst h0
    exact Or.inl (facew_front hc hy fc n ap)
  · exact facew_right hy gt w1 fc n ap hY

/-- Face-offs on top of the race class. -/
def fourFacePlan : Plan where
  S j a b c d e f := fourKeyPlan.S j a b c d e f ∨ (d = 3 ∧ 1 ≤ c ∧ j ≤ 20 ∧ Face j a b c e f)
  W j a b c d e f := fourKeyPlan.W j a b c d e f ∨ (d = 3 ∧ 1 ≤ c ∧ j ≤ 20 ∧ FaceW j a b c e f)
  S_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact fourKeyPlan.S_le h
    · have := h.2.2.1
      omega
  W_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact fourKeyPlan.W_le h
    · have := h.2.2.1
      omega
  strong := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, k⟩
    · rcases fourKeyPlan.strong D h with q | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (strongPush_mono (fun _ _ _ _ _ _ _ w => Or.inl w) q)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inl w⟩
    · obtain ⟨i, rfl, x, y, st, w⟩ := face_step D k
      exact Or.inr ⟨i, rfl, x, y, st, Or.inr ⟨rfl, hc, by omega, w⟩⟩
  weak := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, w⟩
    · obtain ⟨q1, q2, q3⟩ := fourKeyPlan.weak D h
      refine ⟨q1, q2, fun x y st => ?_⟩
      obtain ⟨i, le, s⟩ := q3 x y st
      exact ⟨i, le, Or.inl s⟩
    · have keep := facew_keep w
      refine ⟨keep, weak_reply D (Or.inr (Or.inl (by omega))) keep, fun x y st => ?_⟩
      rcases facew_reply hc w st with ⟨p, m, hm, k⟩ | q
      · exact ⟨j, Nat.le_refl j,
          Or.inl (Or.inr ⟨rfl, hc, hj, Or.inr (Or.inr ⟨p, m, hm, k⟩)⟩)⟩
      · exact ⟨j, Nat.le_refl j, Or.inr ⟨rfl, hc, hj, q⟩⟩

theorem face_le {j a b c e f : Nat} (h : Face j a b c e f) : Face 10 a b c e f := by
  obtain ⟨y, hf, hy, w1, w2, n, -⟩ := h
  refine ⟨y, hf, hy, w1, w2, n, ?_⟩
  unfold FC
  omega

open EndgameChess.KK in
/-- Fourth rank, pawn owner to move: if the king can step onto the lone king's file at most
four files from the pawn, two ranks below a lone king on the seventh or eighth rank, the
pawn owner wins. -/
theorem fresh_four_face_win {σ : Colour} {q : Position} {sk ps wk : Square} {j : Nat}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (k : Face j (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_plan_strong (P := fourFacePlan) (j := 10) h fresh turn safe
    (Or.inr ⟨rank, file, by omega, face_le k⟩)

end EndgameChess.Rules.KPK.Coord
