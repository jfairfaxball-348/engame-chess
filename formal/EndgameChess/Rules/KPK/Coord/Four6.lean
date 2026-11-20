import EndgameChess.Rules.KPK.Coord.Four5

/-! Fourth rank: the lone king on the last rank. It holds by reaching the corresponding
square in time. One file beside the pawn it reaches the guard square `(c,6)` before the king
on the third rank can take the opposition (`PR`). Against a king beside the pawn it waits on
the pawn's file on the last rank, from where it reaches whichever guard square the king's
next step needs (`NB`). Three files out it runs back ahead of a king below it (`QR`),
staying one file nearer the pawn than a king three files out on the fourth rank (`QR2`). -/
namespace EndgameChess.Rules.KPK.Coord

/-- The lone king on the last rank, on a square corresponding to the king's: each shape
gives the king's file and rank and the lone king's file, relative to the pawn. -/
def Ret (a b c e f : Nat) : Prop :=
  f = 7 ∧ ((a + 3 = c ∧ b = 2 ∧ e + 3 = c) ∨
      (a + 3 = c ∧ b = 3 ∧ e + 2 = c) ∨
      (a + 2 = c ∧ b = 2 ∧ e + 1 = c) ∨
      (a + 2 = c ∧ b = 2 ∧ e = c + 1) ∨
      (a + 2 = c ∧ b = 3 ∧ e + 1 = c) ∨
      (a + 1 = c ∧ b = 2 ∧ e + 1 = c) ∨
      (a + 1 = c ∧ b = 2 ∧ e = c + 1) ∨
      (a + 1 = c ∧ b = 3 ∧ e = c) ∨
      (a = c ∧ b = 2 ∧ e + 1 = c) ∨
      (a = c ∧ b = 2 ∧ e = c + 1) ∨
      (a = c + 1 ∧ b = 2 ∧ e + 1 = c) ∨
      (a = c + 1 ∧ b = 2 ∧ e = c + 1) ∨
      (a = c + 1 ∧ b = 3 ∧ e = c) ∨
      (a = c + 2 ∧ b = 2 ∧ e + 1 = c) ∨
      (a = c + 2 ∧ b = 2 ∧ e = c + 1) ∨
      (a = c + 2 ∧ b = 3 ∧ e = c + 1) ∨
      (a = c + 3 ∧ b = 2 ∧ e = c + 3) ∨
      (a = c + 3 ∧ b = 3 ∧ e = c + 2) ∨
      (a = c + 4 ∧ b = 2 ∧ e = c + 3) ∨
      (a = c + 4 ∧ b = 3 ∧ e = c + 3))

/-- The explicit part with the last rank. -/
def C5 (a b c e f : Nat) : Prop := C4 a b c e f ∨ Ret a b c e f

def WC5 (a b c e f : Nat) : Prop :=
  Capture a b c 3 e f ∨ ∃ x y, WeakStep a b c 3 e f x y ∧ C5 a b c x y

theorem wc5_of_wc4 {a b c e f : Nat} (h : WC4 a b c e f) : WC5 a b c e f := by
  rcases h with q | ⟨x, y, st, q⟩
  · exact Or.inl q
  · exact Or.inr ⟨x, y, st, Or.inl q⟩

/-! ## Each last-rank shape answers every king step and the push -/

set_option maxHeartbeats 8000000 in
theorem ret_m3_2_m3_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c) (he : e + 3 = c)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_m3_2_m3_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c) (he : e + 3 = c)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_m3_3_m2_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c) (he : e + 2 = c)
    (st : KingStep a 3 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x = a ∧ y = 2) ∨
      (x = a ∧ y = 4) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a + 1 ∧ y = 4) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_m3_3_m2_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 3 = c) (he : e + 2 = c)
    (fr : Free a 3 e 7 c 4) : W4 a 3 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_m2_2_m1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c) (he : e + 1 = c)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩⟩

set_option maxHeartbeats 8000000 in
theorem ret_m2_2_m1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c) (he : e + 1 = c)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_m2_2_p1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c) (he : e = c + 1)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩⟩

set_option maxHeartbeats 8000000 in
theorem ret_m2_2_p1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c) (he : e = c + 1)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_m2_3_m1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c) (he : e + 1 = c)
    (st : KingStep a 3 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_m2_3_m1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 2 = c) (he : e + 1 = c)
    (fr : Free a 3 e 7 c 4) : W4 a 3 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_m1_2_m1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c) (he : e + 1 = c)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_m1_2_m1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c) (he : e + 1 = c)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_m1_2_p1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c) (he : e = c + 1)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_m1_2_p1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c) (he : e = c + 1)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_m1_3_p0_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c) (he : e = c)
    (st : KingStep a 3 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x + 1 = a ∧ y = 4) ∨
      (x = a ∧ y = 2) ∨
      (x = a ∧ y = 4) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 4) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_m1_3_p0_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a + 1 = c) (he : e = c)
    (fr : Free a 3 e 7 c 4) : W4 a 3 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p0_2_m1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c) (he : e + 1 = c)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))))⟩⟩

set_option maxHeartbeats 8000000 in
theorem ret_p0_2_m1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c) (he : e + 1 = c)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p0_2_p1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c) (he : e = c + 1)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 3) ∨
      (x = a ∧ y = 1) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))⟩⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))))⟩⟩

set_option maxHeartbeats 8000000 in
theorem ret_p0_2_p1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c) (he : e = c + 1)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p1_2_m1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1) (he : e + 1 = c)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p1_2_m1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1) (he : e + 1 = c)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p1_2_p1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1) (he : e = c + 1)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 1) ∨
      (x + 1 = a ∧ y = 2) ∨
      (x = a ∧ y = 1) ∨
      (x = a ∧ y = 3) ∨
      (x = a + 1 ∧ y = 1) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))))⟩⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p1_2_p1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1) (he : e = c + 1)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p1_3_p0_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1) (he : e = c)
    (st : KingStep a 3 c 3 e 7 x y) : WC5 x y c e 7 := by
  have cs : (x + 1 = a ∧ y = 2) ∨
      (x + 1 = a ∧ y = 4) ∨
      (x = a ∧ y = 2) ∨
      (x = a ∧ y = 4) ∨
      (x = a + 1 ∧ y = 2) ∨
      (x = a + 1 ∧ y = 3) ∨
      (x = a + 1 ∧ y = 4) := by
    unfold KingStep Near Apart at st
    omega
  clear st
  rcases cs with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p1_3_p0_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 1) (he : e = c)
    (fr : Free a 3 e 7 c 4) : W4 a 3 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p2_2_m1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2) (he : e + 1 = c)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inr (by unfold GSq; omega)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p2_2_m1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2) (he : e + 1 = c)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p2_2_p1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2) (he : e = c + 1)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))))⟩⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p2_2_p1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2) (he : e = c + 1)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p2_3_p1_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2) (he : e = c + 1)
    (st : KingStep a 3 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))))))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e + 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p2_3_p1_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 2) (he : e = c + 1)
    (fr : Free a 3 e 7 c 4) : W4 a 3 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p3_2_p3_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3) (he : e = c + 3)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))))))))))))⟩⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p3_2_p3_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3) (he : e = c + 3)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p3_3_p2_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3) (he : e = c + 2)
    (st : KingStep a 3 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))))))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p3_3_p2_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 3) (he : e = c + 2)
    (fr : Free a 3 e 7 c 4) : W4 a 3 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p4_2_p3_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 4) (he : e = c + 3)
    (st : KingStep a 2 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))))))))))))⟩⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p4_2_p3_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 4) (he : e = c + 3)
    (fr : Free a 2 e 7 c 4) : W4 a 2 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

set_option maxHeartbeats 8000000 in
theorem ret_p4_3_p3_k {a c e x y : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 4) (he : e = c + 3)
    (st : KingStep a 3 c 3 e 7 x y) : WC5 x y c e 7 := by
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
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 7, by unfold WeakStep Near Apart Att; omega, Or.inr ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))))))))))))))⟩⟩
  · exact Or.inr ⟨e, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inr (Or.inl (by unfold Opd; omega)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩
  · exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, Or.inl (Or.inl (Or.inl (by s3t)))⟩

set_option maxHeartbeats 8000000 in
theorem ret_p4_3_p3_p {a c e : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (ha : a = c + 4) (he : e = c + 3)
    (fr : Free a 3 e 7 c 4) : W4 a 3 c e 7 := by
  unfold Free at fr
  exact Or.inr ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega, by s4t⟩

theorem ret_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : Ret a b c e f)
    (st : KingStep a b c 3 e f x y) : WC5 x y c e f := by
  have h3 := D.bounds.2.2.1
  obtain ⟨rfl, s⟩ := h
  rcases s with ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩
  · exact ret_m3_2_m3_k hc h3 ha he st
  · exact ret_m3_3_m2_k hc h3 ha he st
  · exact ret_m2_2_m1_k hc h3 ha he st
  · exact ret_m2_2_p1_k hc h3 ha he st
  · exact ret_m2_3_m1_k hc h3 ha he st
  · exact ret_m1_2_m1_k hc h3 ha he st
  · exact ret_m1_2_p1_k hc h3 ha he st
  · exact ret_m1_3_p0_k hc h3 ha he st
  · exact ret_p0_2_m1_k hc h3 ha he st
  · exact ret_p0_2_p1_k hc h3 ha he st
  · exact ret_p1_2_m1_k hc h3 ha he st
  · exact ret_p1_2_p1_k hc h3 ha he st
  · exact ret_p1_3_p0_k hc h3 ha he st
  · exact ret_p2_2_m1_k hc h3 ha he st
  · exact ret_p2_2_p1_k hc h3 ha he st
  · exact ret_p2_3_p1_k hc h3 ha he st
  · exact ret_p3_2_p3_k hc h3 ha he st
  · exact ret_p3_3_p2_k hc h3 ha he st
  · exact ret_p4_2_p3_k hc h3 ha he st
  · exact ret_p4_3_p3_k hc h3 ha he st

theorem ret_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : Ret a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  have h3 := D.bounds.2.2.1
  obtain ⟨rfl, s⟩ := h
  rcases s with ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩ | ⟨ha, rfl, he⟩
  · exact ret_m3_2_m3_p hc h3 ha he fr
  · exact ret_m3_3_m2_p hc h3 ha he fr
  · exact ret_m2_2_m1_p hc h3 ha he fr
  · exact ret_m2_2_p1_p hc h3 ha he fr
  · exact ret_m2_3_m1_p hc h3 ha he fr
  · exact ret_m1_2_m1_p hc h3 ha he fr
  · exact ret_m1_2_p1_p hc h3 ha he fr
  · exact ret_m1_3_p0_p hc h3 ha he fr
  · exact ret_p0_2_m1_p hc h3 ha he fr
  · exact ret_p0_2_p1_p hc h3 ha he fr
  · exact ret_p1_2_m1_p hc h3 ha he fr
  · exact ret_p1_2_p1_p hc h3 ha he fr
  · exact ret_p1_3_p0_p hc h3 ha he fr
  · exact ret_p2_2_m1_p hc h3 ha he fr
  · exact ret_p2_2_p1_p hc h3 ha he fr
  · exact ret_p2_3_p1_p hc h3 ha he fr
  · exact ret_p3_2_p3_p hc h3 ha he fr
  · exact ret_p3_3_p2_p hc h3 ha he fr
  · exact ret_p4_2_p3_p hc h3 ha he fr
  · exact ret_p4_3_p3_p hc h3 ha he fr

/-! ## The region -/

theorem c5_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : C5 a b c e f)
    (st : KingStep a b c 3 e f x y) : WC5 x y c e f := by
  rcases h with h | h
  · exact wc5_of_wc4 (c4_king D hc h st)
  · exact ret_king D hc h st

theorem c5_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : C5 a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  rcases h with h | h
  · exact c4_push D hc h fr
  · exact ret_push D hc h fr

/-- A tempo position answered into the explicit part. -/
def T5 (a b c e f : Nat) : Prop :=
  (f = 7 ∨ e = c + 4 ∨ e + 4 = c ∨ b = 7) ∧
    (∀ x y, KingStep a b c 3 e f x y → WC5 x y c e f) ∧ (Free a b e f c 4 → W4 a b c e f)

/-- The fourth-rank draw region. -/
def R5 (a b c e f : Nat) : Prop := C5 a b c e f ∨ T5 a b c e f

def WR5 (a b c e f : Nat) : Prop :=
  Capture a b c 3 e f ∨ ∃ x y, WeakStep a b c 3 e f x y ∧ R5 a b c x y

theorem wr5_of_wc5 {a b c e f : Nat} (h : WC5 a b c e f) : WR5 a b c e f := by
  rcases h with q | ⟨x, y, st, q⟩
  · exact Or.inl q
  · exact Or.inr ⟨x, y, st, Or.inl q⟩

theorem r5_king {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : R5 a b c e f)
    (st : KingStep a b c 3 e f x y) : WR5 x y c e f := by
  rcases h with h | ⟨-, k, -⟩
  · exact wr5_of_wc5 (c5_king D hc h st)
  · exact wr5_of_wc5 (k x y st)

theorem r5_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : R5 a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  rcases h with h | ⟨-, -, p⟩
  · exact c5_push D hc h fr
  · exact p fr

/-- Pawn on the fourth to seventh rank, any non-rook file, with the full fourth-rank
region. -/
def fourGuard5 : Guard where
  S a b c d e f := fiveGuard.S a b c d e f ∨ knFiveGuard.S a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ R5 a b c e f)
  W a b c d e f := fiveGuard.W a b c d e f ∨ knFiveGuard.W a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ WR5 a b c e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | h | ⟨rfl, hc, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := fiveGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r),
        fun p r t => Or.inl (q3 p r t), q4⟩
    · obtain ⟨q1, q2, q3, q4⟩ := knFiveGuard.strong D h
      exact ⟨fun x y s => Or.inr (Or.inl (q1 x y s)), fun p r => Or.inr (Or.inl (q2 p r)),
        fun p r t => Or.inr (Or.inl (q3 p r t)), q4⟩
    · refine ⟨fun x y st => Or.inr (Or.inr ⟨rfl, hc, r5_king D hc h st⟩), fun fr _ => ?_,
        fun q => by omega, fun q => by omega⟩
      have w := r5_push D hc h fr
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
theorem fresh_four_hold5 {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (sat : R5 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong (G := fourGuard5) h fresh turn safe (Or.inr (Or.inr ⟨rank, file, sat⟩))

open EndgameChess.KK in
/-- Non-rook pawn on the fourth rank, lone king to move: it holds if it takes the pawn or
steps into the region. -/
theorem fresh_four_weak_hold5 {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (w : WR5 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_weak (G := fourGuard5) h fresh turn (Or.inr (Or.inr ⟨rank, file, w⟩))

end EndgameChess.Rules.KPK.Coord
