import EndgameChess.Rules.KPK.Coord.Sixth

/-! The lone king's race to the squares ahead of the pawn. A step towards the square two
ahead of a pawn on the fifth rank brings it closer to every key square at once. -/
namespace EndgameChess.Rules.KPK.Coord

/-- One step towards `(g,h)`. -/
def Toward (e f g h u v : Nat) : Prop :=
  ((e < g ∧ u = e + 1) ∨ (g < e ∧ u + 1 = e) ∨ (e = g ∧ u = e)) ∧
  ((f < h ∧ v = f + 1) ∨ (h < f ∧ v + 1 = f) ∨ (f = h ∧ v = f))

/-- Stepping towards the centre keeps every race of length at least one. -/
theorem race_keep {e f u v c p q n : Nat} (hp : c ≤ p + 1 ∧ p ≤ c + 1) (hq : q = 5 ∨ q = 6) (hn : 1 ≤ n)
    (w : Ch e f p q (n + 1)) (t : Toward e f c 6 u v) : Ch u v p q n := by
  unfold Ch at *
  unfold Toward at t
  omega

/-- A king step changes a distance by at most one. -/
theorem ch_step {a b x y p q n : Nat} (s : Near a b x y) (h : Ch x y p q n) : Ch a b p q (n + 1) := by
  unfold Ch at *
  unfold Near at s
  omega

/-- The only shortest way to `(p,q)` runs through the pawn on `(c,4)`. -/
def Thru (a b c p q : Nat) : Prop :=
  (q = 5 ∧ p = c + 1 ∧ a + 4 = c + b ∧ a < c) ∨ (q = 5 ∧ p + 1 = c ∧ a + b = c + 4 ∧ c < a)

/-- The king reaches `(p,q)` within `n` moves, going round the pawn. -/
def KR (a b c p q n : Nat) : Prop :=
  Ch a b p q n ∧ (¬ Thru a b c p q ∨ Ch a b p q (n - 1) ∧ 1 ≤ n)

/-- The lone king must cross the pawn's file above the pawn's attacks. -/
def Cross (e f c p : Nat) : Prop := f ≤ 5 ∧ ((e < c ∧ c < p) ∨ (c < e ∧ p < c))

/-- A diagonal to the crossing point runs over an attacked square. -/
def Hit (e f c : Nat) : Prop := (e + f = c + 6 ∧ c + 2 ≤ e) ∨ (e + 6 = c + f ∧ e + 2 ≤ c)

/-- The lone king reaches `(p,q)` within `n` moves, going round the attacked squares. -/
def WR (e f c p q n : Nat) : Prop :=
  Ch e f p q n ∧ (¬ Cross e f c p ∨ (1 ≤ n ∧ Ch e f c 6 (n - 1) ∧ (¬ Hit e f c ∨ (2 ≤ n ∧ Ch e f c 6 (n - 2)))))

set_option maxHeartbeats 4000000 in
theorem kr_step {a b c p q x y n : Nat} (hc : 2 ≤ c) (hp : p = c + 1 ∨ p + 1 = c) (hq : q = 5 ∨ q = 6)
    (s : Near a b x y) (np : ¬ (x = c ∧ y = 4)) (h : KR x y c p q n) : KR a b c p q (n + 1) := by
  unfold KR Thru Ch at *
  unfold Near at s
  omega

set_option maxHeartbeats 4000000 in
theorem wr_step {e f c p q u v n : Nat} (hc : 2 ≤ c) (hp : p = c + 1 ∨ p + 1 = c) (hq : q = 5 ∨ q = 6)
    (hn : 1 ≤ n) (t : Toward e f c 6 u v) (safe : ¬ (v = 5 ∧ (u = c + 1 ∨ u + 1 = c)))
    (h : WR e f c p q (n + 1)) : WR u v c p q n := by
  unfold WR Cross Hit Ch at *
  unfold Toward at t
  omega

end EndgameChess.Rules.KPK.Coord
