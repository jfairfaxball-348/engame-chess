import EndgameChess.Rules.KPK.Coord.SevenWin

/-! Wins with a bishop or centre pawn on the sixth rank, outside the guard. The king
gets beside or ahead of the pawn unopposed, or the pawn runs. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- Lone king to move, pawn on the seventh: no capture, and every reply leaves the guard. -/
def W6 (a b c e f : Nat) : Prop :=
  ¬ Capture a b c 6 e f ∧ (∃ x y, WeakStep a b c 6 e f x y) ∧
    ∀ x y, WeakStep a b c 6 e f x y → ¬ TS a b c 6 x y

/-- A push with the king beside or ahead of the pawn. -/
theorem w6_side {a b c e f t o u : Nat} (D : Dom a b c 6 e f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (ha : a = t) (hb : b = 6 ∨ b = 7) : W6 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  have r : R6 a b c 6 := by
    unfold Sd at sd
    unfold R6
    omega
  have keep : ¬ Capture a b c 6 e f := by
    unfold Sd at sd
    unfold Capture Near
    omega
  refine ⟨keep, key_reply D (by omega) keep (Or.inr r), ?_⟩
  intro x y st h
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  have a7 := st.k7
  unfold Sd at sd
  obtain ⟨-, -, q | q | q⟩ := h
  · unfold Block7 at q; omega
  · unfold SideL Within1 at q; omega
  · unfold SideR Within1 at q; omega

/-- A pawn the lone king cannot catch: every reply stays off the top guard squares. -/
theorem w6_run {a b c e f : Nat} (D : Dom a b c 6 e f) (hc : 2 ≤ c) (out : Outside 2 c e f) :
    W6 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Outside at out
  have keep : ¬ Capture a b c 6 e f := by
    unfold Capture Near
    omega
  refine ⟨keep, weak_reply D (by omega) keep, ?_⟩
  intro x y st h
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  obtain ⟨-, -, q | q | q⟩ := h
  · unfold Block7 at q; omega
  · unfold SideL at q; omega
  · unfold SideR at q; omega

/-- A key square ends the guard. -/
theorem nd_key {a b c e f : Nat} (k : Key5 a b c) : ¬ S5 a b c e f := fun h => h.1 k

/-- A king beside the pawn is stopped only directly opposite. -/
theorem nd_beside {a b c e f : Nat} (k : Beside a b c) (no : ¬ (e = a ∧ f = 7)) : ¬ S5 a b c e f := by
  rintro ⟨-, -, -, -, ⟨-, h1, h2⟩ | ⟨nb, -⟩⟩
  · exact no ⟨h1, h2⟩
  · exact nb k

set_option maxHeartbeats 4000000 in
/-- A king close to the pawn beats a lone king not yet on a blockade square. -/
theorem nd_close {x y c p q : Nat} (hc : 2 ≤ c) (a1 : ¬ Arr 1 x y c) (p2 : Ch x y c 5 2)
    (nbs : ¬ Beside x y c) (y7 : y ≠ 7 ∨ q ≠ 5) (b0 : ¬ Bl 0 c p q) : ¬ S5 x y c p q := by
  rintro ⟨k, -, -, -, ⟨bs, h1, h2⟩ | ⟨nb, h⟩⟩
  · exact nbs bs
  · have a2 : ¬ Arr 2 x y c := by
      unfold Arr Ch at a1 ⊢
      omega
    unfold Ch at p2
    rcases h with A | ⟨B, R⟩ | ⟨B, R⟩ | ⟨B, R⟩ | ⟨-, -, -, R⟩ | ⟨-, F⟩ | ⟨-, F⟩ | ⟨-, F⟩
    · omega
    · exact b0 B
    · exact a1 R
    · exact a2 R
    · exact a1 R
    · exact F (by unfold Ch; omega)
    · exact F (by unfold Ch; omega)
    · exact F (by unfold Ch; omega)

/-- Phase of the king on the way to the pawn. -/
def Phi (j a b c : Nat) : Prop :=
  (((a = c + 1 ∨ a + 1 = c) ∧ 6 ≤ b)) ∨ (1 ≤ j ∧ ((a = c ∧ 6 ≤ b) ∨ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7))) ∨
    (2 ≤ j ∧ Beside a b c) ∨ (3 ≤ j ∧ a = c ∧ b = 4) ∨ (3 ≤ j ∧ Ch a b c 4 (j - 3))

/-- Lone king to move on the sixth rank: no capture, a reply, and no reply reaches the guard. -/
def W5win (j a b c e f : Nat) : Prop :=
  Phi j a b c ∧ ¬ Capture a b c 5 e f ∧ (∃ x y, WeakStep a b c 5 e f x y) ∧
    ∀ x y, WeakStep a b c 5 e f x y → ¬ S5 a b c x y

set_option maxHeartbeats 4000000 in
/-- The lone king has a move unless it is stalemated next to the king and the sixth-rank pawn. -/
theorem six_reply {a b c e f : Nat} (D : Dom a b c 5 e f) (hc : 2 ≤ c) (keep : ¬ Capture a b c 5 e f)
    (no : ¬ (c = 2 ∧ e = 0 ∧ f = 7 ∧ a = 1 ∧ b = 5)) : ∃ x y, WeakStep a b c 5 e f x y := by
  by_cases top : f ≤ 6 ∨ 5 ≤ 4 ∨ c + 2 < e ∨ e + 2 < c
  · exact weak_reply D top keep
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  apply Classical.byContradiction
  intro none
  have t (x y : Nat) : ¬ WeakStep a b c 5 e f x y := fun s => none ⟨x, y, s⟩
  have h1 := t (e + 1) f
  have h2 := t (e - 1) f
  have h4 := t e (f - 1)
  have h5 := t (e + 1) (f - 1)
  have h6 := t (e - 1) (f - 1)
  unfold WeakStep Near Apart Att at h1 h2 h4 h5 h6
  have z : f = 7 := by omega
  subst z
  rcases Nat.lt_trichotomy e c with g | g | g <;> omega

/-- The king steps beside the pawn on the side `t` unopposed. -/
def SN (a b c e f t : Nat) : Prop :=
  Near a b t 5 ∧ Apart t 5 e f ∧ ((e = t ∧ f = 7) ∨ ¬ Near e f t 7) ∧
    ¬ (c = 2 ∧ t = 1 ∧ e = 0 ∧ f = 7)

/-- The king is next to a key square and the lone king on the far side of the pawn. -/
def SP (a b c e f t o u : Nat) : Prop := Ch a b t 6 1 ∧ (e = o ∨ e = u) ∧ 6 ≤ f

/-- The classes left once the king is not on a key, beside the pawn or two files out on
the last rank. -/
def Step5 (a b c e f : Nat) : Prop :=
  SN a b c e f (c + 1) ∨ SN a b c e f (c - 1) ∨ SP a b c e f (c + 1) (c - 1) (c - 2) ∨
    SP a b c e f (c - 1) (c + 1) (c + 2) ∨ (Ch a b c 4 1 ∧ ¬ (a = c ∧ b = 4) ∧ ¬ Bl 1 c e f) ∨
    ((e = c + 2 ∨ e + 2 = c) ∧ ¬ Arr 2 a b c)

end EndgameChess.Rules.KPK.Coord
