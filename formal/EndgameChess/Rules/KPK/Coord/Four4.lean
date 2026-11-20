import EndgameChess.Rules.KPK.Coord.Four3

/-! Fourth rank: the exact region. To the lifted region `S3` it adds kings opposed on a
file outside the pawn (`Opp`), which hold by keeping the opposition, and tempo positions
(`T3`). A tempo position is one where the lift misjudges a king by one move: the lone king
on the last rank, the lone king four files from the pawn, or the king on the last rank.
It belongs to the region when every strong move can be answered by a step into `S3` or
`Opp`. This answers into the proved part once; it is not repeated. -/
namespace EndgameChess.Rules.KPK.Coord

/-- Kings opposed on one file outside the pawn: one file out with the king on the last
rank; two files out with the lone king on the sixth rank and the king on the fourth or last
rank; three files out with the king on the third or fourth rank below the lone king. -/
def Opp (a b c e f : Nat) : Prop :=
  e = a ∧ ((f = 5 ∧ b = 7 ∧ (a = c + 1 ∨ a + 1 = c)) ∨
    (f = 5 ∧ (b = 3 ∨ b = 7) ∧ (a = c + 2 ∨ a + 2 = c)) ∨
    ((a = c + 3 ∨ a + 3 = c) ∧ ((b = 2 ∧ (f = 5 ∨ f = 6)) ∨ (b = 3 ∧ f = 5))))

/-- The explicit part of the fourth-rank region. -/
def C3 (a b c e f : Nat) : Prop := S3 a b c e f ∨ Opp a b c e f

/-- The lone king's answer into the explicit part. -/
def WC3 (a b c e f : Nat) : Prop :=
  Capture a b c 3 e f ∨ ∃ x y, WeakStep a b c 3 e f x y ∧ C3 a b c x y

/-- A race keeping the king's way round the pawn. -/
macro "race2" : tactic =>
  `(tactic| (intro n kr; unfold KR Thru Ch at kr; unfold WR Cross Hit Ch; omega))

macro "m4d" : tactic =>
  `(tactic| (refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> first | race2 | ocs))

/-- The clauses of `S4` other than a king beside the pawn. -/
macro "s4r" : tactic => `(tactic| first
  | exact Or.inl (by unfold Op4; omega)
  | exact Or.inr (Or.inr (Or.inl ⟨by unfold Near; omega, by unfold Near; omega,
      by intro p q n1 n2; unfold Near at n1 n2; unfold Apart; omega⟩))
  | exact Or.inr (Or.inl (m4_center (by omega) (by omega) (by omega) (by unfold K4; omega)))
  | exact Or.inr (Or.inl (by m4d)))

macro "s4t" : tactic => `(tactic| first
  | exact ⟨by unfold K4; omega, by unfold Sq4; omega,
      Or.inl ⟨by unfold B4; omega, by omega, by omega⟩⟩
  | (refine ⟨by unfold K4; omega, by unfold Sq4; omega, Or.inr ⟨by unfold B4; omega, ?_⟩⟩
     s4r))

macro "s3t" : tactic => `(tactic| (refine ⟨by omega, ?_⟩; first
  | (refine ⟨_, Or.inl ⟨by omega, rfl⟩, by unfold Apart; omega, ?_⟩; s4t)
  | (refine ⟨7, Or.inr ⟨by omega, rfl⟩, by unfold Apart; omega, ?_⟩; s4t)))

/-! ## Each opposition shape answers every king step and the push -/

set_option maxHeartbeats 8000000 in
theorem opp_1_7_5_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c)
    (st : KingStep a 7 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x = a + 1 ∧ y = 7) ∨
      (x + 1 = a ∧ y = 7) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_1_7_5_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c)
    (fr : Free a 7 a 5 c 4) : W4 a 7 c a 5 := by
  unfold Free at fr
  exact Or.inl (by unfold Capture Near; omega)

set_option maxHeartbeats 8000000 in
theorem opp_1_7_5_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1)
    (st : KingStep a 7 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x + 1 = a ∧ y = 7) ∨
      (x = a + 1 ∧ y = 7) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_1_7_5_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1)
    (fr : Free a 7 a 5 c 4) : W4 a 7 c a 5 := by
  unfold Free at fr
  exact Or.inl (by unfold Capture Near; omega)

set_option maxHeartbeats 8000000 in
theorem opp_2_3_5_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (st : KingStep a 3 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_2_3_5_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (fr : Free a 3 a 5 c 4) : W4 a 3 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a + 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_2_3_5_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (st : KingStep a 3 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 2) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_2_3_5_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (fr : Free a 3 a 5 c 4) : W4 a 3 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_2_7_5_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (st : KingStep a 7 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x = a + 1 ∧ y = 7) ∨
      (x + 1 = a ∧ y = 7) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_2_7_5_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c)
    (fr : Free a 7 a 5 c 4) : W4 a 7 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_2_7_5_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (st : KingStep a 7 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x + 1 = a ∧ y = 7) ∨
      (x = a + 1 ∧ y = 7) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_2_7_5_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2)
    (fr : Free a 7 a 5 c 4) : W4 a 7 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_5_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c)
    (st : KingStep a 2 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_5_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c)
    (fr : Free a 2 a 5 c 4) : W4 a 2 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_5_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3)
    (st : KingStep a 2 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_5_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3)
    (fr : Free a 2 a 5 c 4) : W4 a 2 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_6_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c)
    (st : KingStep a 2 c 3 a 6 x y) : WC3 x y c a 6 := by
  have cs : (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_6_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c)
    (fr : Free a 2 a 6 c 4) : W4 a 2 c a 6 := by
  unfold Free at fr
  exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_6_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3)
    (st : KingStep a 2 c 3 a 6 x y) : WC3 x y c a 6 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_2_6_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3)
    (fr : Free a 2 a 6 c 4) : W4 a 2 c a 6 := by
  unfold Free at fr
  exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_3_5_l_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c)
    (st : KingStep a 3 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a ∧ y = 2) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a + 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_3_5_l_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c)
    (fr : Free a 3 a 5 c 4) : W4 a 3 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a + 1, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_3_5_r_k {a c x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3)
    (st : KingStep a 3 c 3 a 5 x y) : WC3 x y c a 5 := by
  have cs : (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 2) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, Or.inr (by unfold Opp; omega)⟩
  · exact Or.inr ⟨a, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩
  · exact Or.inr ⟨a - 1, 4, by unfold WeakStep Near Apart Att; omega, Or.inl (by s3t)⟩

set_option maxHeartbeats 8000000 in
theorem opp_3_3_5_r_p {a c : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3)
    (fr : Free a 3 a 5 c 4) : W4 a 3 c a 5 := by
  unfold Free at fr
  exact Or.inr ⟨a - 1, 5, by unfold WeakStep Near Apart Att; omega, by s4t⟩

/-- Every king step from an opposition position is answered into the explicit part. -/
theorem opp_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : Opp a b c e f)
    (st : KingStep a b c 3 e f x y) : WC3 x y c e f := by
  have h3 := D.bounds.2.2.1
  obtain ⟨he, h⟩ := h
  subst he
  rcases h with ⟨rfl, rfl, s | s⟩ | ⟨rfl, rfl | rfl, s | s⟩ |
    ⟨s | s, ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact opp_1_7_5_r_k hc h3 (by omega) st
  · exact opp_1_7_5_l_k hc h3 (by omega) st
  · exact opp_2_3_5_r_k hc h3 (by omega) st
  · exact opp_2_3_5_l_k hc h3 (by omega) st
  · exact opp_2_7_5_r_k hc h3 (by omega) st
  · exact opp_2_7_5_l_k hc h3 (by omega) st
  · exact opp_3_2_5_r_k hc h3 (by omega) st
  · exact opp_3_2_6_r_k hc h3 (by omega) st
  · exact opp_3_3_5_r_k hc h3 (by omega) st
  · exact opp_3_2_5_l_k hc h3 (by omega) st
  · exact opp_3_2_6_l_k hc h3 (by omega) st
  · exact opp_3_3_5_l_k hc h3 (by omega) st

/-- After a push from an opposition position the lone king has its fifth-rank answer. -/
theorem opp_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : Opp a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  have h3 := D.bounds.2.2.1
  obtain ⟨he, h⟩ := h
  subst he
  rcases h with ⟨rfl, rfl, s | s⟩ | ⟨rfl, rfl | rfl, s | s⟩ |
    ⟨s | s, ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact opp_1_7_5_r_p hc h3 (by omega) fr
  · exact opp_1_7_5_l_p hc h3 (by omega) fr
  · exact opp_2_3_5_r_p hc h3 (by omega) fr
  · exact opp_2_3_5_l_p hc h3 (by omega) fr
  · exact opp_2_7_5_r_p hc h3 (by omega) fr
  · exact opp_2_7_5_l_p hc h3 (by omega) fr
  · exact opp_3_2_5_r_p hc h3 (by omega) fr
  · exact opp_3_2_6_r_p hc h3 (by omega) fr
  · exact opp_3_3_5_r_p hc h3 (by omega) fr
  · exact opp_3_2_5_l_p hc h3 (by omega) fr
  · exact opp_3_2_6_l_p hc h3 (by omega) fr
  · exact opp_3_3_5_l_p hc h3 (by omega) fr

/-! ## Tempo positions and the region -/

/-- A king misjudged by one move by the lift, and every strong move answered into the
explicit part. -/
def T3 (a b c e f : Nat) : Prop :=
  (f = 7 ∨ e = c + 4 ∨ e + 4 = c ∨ b = 7) ∧
    (∀ x y, KingStep a b c 3 e f x y → WC3 x y c e f) ∧ (Free a b e f c 4 → W4 a b c e f)

/-- The fourth-rank draw region. -/
def R3 (a b c e f : Nat) : Prop := C3 a b c e f ∨ T3 a b c e f

/-- The lone king's answer into the region. -/
def WR3 (a b c e f : Nat) : Prop :=
  Capture a b c 3 e f ∨ ∃ x y, WeakStep a b c 3 e f x y ∧ R3 a b c x y

theorem wr3_of_wc3 {a b c e f : Nat} (h : WC3 a b c e f) : WR3 a b c e f := by
  rcases h with q | ⟨x, y, st, q⟩
  · exact Or.inl q
  · exact Or.inr ⟨x, y, st, Or.inl q⟩

theorem wc3_of_w3 {a b c e f : Nat} (h : W3 a b c e f) : WC3 a b c e f := by
  rcases h with q | ⟨x, y, st, q⟩
  · exact Or.inl q
  · exact Or.inr ⟨x, y, st, Or.inl q⟩

/-- The explicit part is closed. -/
theorem c3_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : C3 a b c e f)
    (st : KingStep a b c 3 e f x y) : WC3 x y c e f := by
  rcases h with h | h
  · exact wc3_of_w3 (s3_king D hc h st)
  · exact opp_king D hc h st

theorem c3_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : C3 a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  rcases h with h | h
  · exact s3_push D hc h fr
  · exact opp_push D hc h fr

/-- The region is closed under king steps. -/
theorem r3_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : R3 a b c e f)
    (st : KingStep a b c 3 e f x y) : WR3 x y c e f := by
  rcases h with h | ⟨-, k, -⟩
  · exact wr3_of_wc3 (c3_king D hc h st)
  · exact wr3_of_wc3 (k x y st)

theorem r3_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : R3 a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  rcases h with h | ⟨-, -, p⟩
  · exact c3_push D hc h fr
  · exact p fr

/-- Pawn on the fourth to seventh rank, any non-rook file, with the full fourth-rank
region. -/
def fourGuardR : Guard where
  S a b c d e f := fiveGuard.S a b c d e f ∨ knFiveGuard.S a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ R3 a b c e f)
  W a b c d e f := fiveGuard.W a b c d e f ∨ knFiveGuard.W a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ WR3 a b c e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | h | ⟨rfl, hc, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := fiveGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r),
        fun p r t => Or.inl (q3 p r t), q4⟩
    · obtain ⟨q1, q2, q3, q4⟩ := knFiveGuard.strong D h
      exact ⟨fun x y s => Or.inr (Or.inl (q1 x y s)), fun p r => Or.inr (Or.inl (q2 p r)),
        fun p r t => Or.inr (Or.inl (q3 p r t)), q4⟩
    · refine ⟨fun x y st => Or.inr (Or.inr ⟨rfl, hc, r3_king D hc h st⟩), fun fr _ => ?_,
        fun q => by omega, fun q => by omega⟩
      have w := r3_push D hc h fr
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
/-- Non-rook pawn on the fourth rank, pawn owner to move, root in the region: the lone king
holds, and no forced mate exists at any length. -/
theorem fresh_four_hold_r {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (sat : R3 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong (G := fourGuardR) h fresh turn safe (Or.inr (Or.inr ⟨rank, file, sat⟩))

open EndgameChess.KK in
/-- Non-rook pawn on the fourth rank, lone king to move: it holds if it takes the pawn or
steps into the region. -/
theorem fresh_four_weak_hold_r {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (w : WR3 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_weak (G := fourGuardR) h fresh turn (Or.inr (Or.inr ⟨rank, file, w⟩))

end EndgameChess.Rules.KPK.Coord
