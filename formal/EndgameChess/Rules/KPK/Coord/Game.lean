
/-! Abstract coordinate game of exact KPK, with oriented heights and the pawn
on files `0..3`. Every predicate is a linear condition on natural numbers.
The moves are connected to the rules kernel in `Coord/Bridge`. -/
namespace EndgameChess.Rules.KPK.Coord

/-- Two squares at Chebyshev distance at least two. -/
def Apart (a b e f : Nat) : Prop := a + 2 ≤ e ∨ e + 2 ≤ a ∨ b + 2 ≤ f ∨ f + 2 ≤ b

/-- Two distinct squares at Chebyshev distance one. -/
def Near (a b e f : Nat) : Prop :=
  a ≤ e + 1 ∧ e ≤ a + 1 ∧ b ≤ f + 1 ∧ f ≤ b + 1 ∧ ¬ (a = e ∧ b = f)

/-- The pawn attacks exactly one rank forward on the adjacent files. -/
def Att (c d e f : Nat) : Prop := f = d + 1 ∧ (e = c + 1 ∨ e + 1 = c)

/-- Admissible coordinates for either turn. -/
def Dom (a b c d e f : Nat) : Prop :=
  a ≤ 7 ∧ b ≤ 7 ∧ c ≤ 3 ∧ 1 ≤ d ∧ d ≤ 6 ∧ e ≤ 7 ∧ f ≤ 7 ∧
    ¬ (a = c ∧ b = d) ∧ ¬ (e = c ∧ f = d) ∧ Apart a b e f

/-- Admissible coordinates with the pawn owner to move. -/
def DomS (a b c d e f : Nat) : Prop := Dom a b c d e f ∧ ¬ Att c d e f

/-- A legal quiet king step of the pawn owner. -/
def KingStep (a b c d e f a' b' : Nat) : Prop :=
  Near a b a' b' ∧ a' ≤ 7 ∧ b' ≤ 7 ∧ ¬ (a' = c ∧ b' = d) ∧ Apart a' b' e f

/-- A legal non-capturing step of the lone king. -/
def WeakStep (a b c d e f e' f' : Nat) : Prop :=
  Near e f e' f' ∧ e' ≤ 7 ∧ f' ≤ 7 ∧ ¬ (e' = c ∧ f' = d) ∧ Apart a b e' f' ∧ ¬ Att c d e' f'

/-- The lone king can legally capture the pawn. -/
def Capture (a b c d e f : Nat) : Prop := Near e f c d ∧ ¬ Near a b c d

/-- No square on the two lines of a rook on `(c,7)`. -/
def OffRook (c x y : Nat) : Prop := x ≠ c ∧ y ≠ 7

/-- No square on the lines of a queen on `(c,7)`. -/
def OffQueen (c x y : Nat) : Prop := OffRook c x y ∧ x + 7 ≠ c + y ∧ x + y ≠ c + 7

/-- A promoted piece on `(c,7)` cannot be captured at once. -/
def PieceSafe (a b c e f : Nat) : Prop := ¬ Capture a b c 7 e f

/-- The defending king stands on the last rank, unobstructed. -/
def RankCheck (a b c e f : Nat) : Prop :=
  f = 7 ∧ ¬ (b = 7 ∧ ((c < a ∧ a < e) ∨ (e < a ∧ a < c)))

/-- The defending king stands on the promotion file, unobstructed. -/
def FileCheck (a b c e f : Nat) : Prop := e = c ∧ ¬ (a = c ∧ f < b)

/-- A legal escape shielded from a piece on `(c,7)` by the strong king on the file. -/
def Shielded (a b c x y : Nat) : Prop := x = c ∧ a = c ∧ y < b

/-- A queen promotion that wins by a check or by leaving a legal reply. -/
def QueenGood (a b c e f : Nat) : Prop :=
  PieceSafe a b c e f ∧ (RankCheck a b c e f ∨ FileCheck a b c e f ∨
    ∃ x y, Near e f x y ∧ x ≤ 7 ∧ y ≤ 7 ∧ ¬ (x = c ∧ y = 7) ∧ Apart a b x y ∧
      (OffQueen c x y ∨ Shielded a b c x y))

/-- A rook promotion that wins by a check or by leaving a legal reply. -/
def RookGood (a b c e f : Nat) : Prop :=
  PieceSafe a b c e f ∧ (RankCheck a b c e f ∨ FileCheck a b c e f ∨
    ∃ x y, Near e f x y ∧ x ≤ 7 ∧ y ≤ 7 ∧ ¬ (x = c ∧ y = 7) ∧ Apart a b x y ∧
      (OffRook c x y ∨ Shielded a b c x y))

/-- The promotion square is free. -/
def Free (a b e f x y : Nat) : Prop := ¬ (a = x ∧ b = y) ∧ ¬ (e = x ∧ f = y)

theorem Dom.bounds {a b c d e f : Nat} (D : Dom a b c d e f) :
    a ≤ 7 ∧ b ≤ 7 ∧ c ≤ 3 ∧ 1 ≤ d ∧ d ≤ 6 ∧ e ≤ 7 ∧ f ≤ 7 :=
  ⟨D.1, D.2.1, D.2.2.1, D.2.2.2.1, D.2.2.2.2.1, D.2.2.2.2.2.1, D.2.2.2.2.2.2.1⟩

theorem DomS.bounds {a b c d e f : Nat} (D : DomS a b c d e f) :
    a ≤ 7 ∧ b ≤ 7 ∧ c ≤ 3 ∧ 1 ≤ d ∧ d ≤ 6 ∧ e ≤ 7 ∧ f ≤ 7 := Dom.bounds D.1

theorem Near.bounds {a b e f : Nat} (N : Near a b e f) :
    a ≤ e + 1 ∧ e ≤ a + 1 ∧ b ≤ f + 1 ∧ f ≤ b + 1 := ⟨N.1, N.2.1, N.2.2.1, N.2.2.2.1⟩

theorem KingStep.bounds {a b c d e f x y : Nat} (s : KingStep a b c d e f x y) :
    (a ≤ x + 1 ∧ x ≤ a + 1 ∧ b ≤ y + 1 ∧ y ≤ b + 1) ∧ x ≤ 7 ∧ y ≤ 7 :=
  ⟨Near.bounds s.1, s.2.1, s.2.2.1⟩

theorem WeakStep.bounds {a b c d e f x y : Nat} (s : WeakStep a b c d e f x y) :
    (e ≤ x + 1 ∧ x ≤ e + 1 ∧ f ≤ y + 1 ∧ y ≤ f + 1) ∧ x ≤ 7 ∧ y ≤ 7 :=
  ⟨Near.bounds s.1, s.2.1, s.2.2.1⟩

theorem Dom.k1 {a b c d e f : Nat} (D : Dom a b c d e f) :
    a + 2 ≤ e ∨ e + 2 ≤ a ∨ b + 2 ≤ f ∨ f + 2 ≤ b := D.2.2.2.2.2.2.2.2.2

theorem Dom.k2 {a b c d e f : Nat} (D : Dom a b c d e f) : ¬ (a = c ∧ b = d) := D.2.2.2.2.2.2.2.1

theorem Dom.k3 {a b c d e f : Nat} (D : Dom a b c d e f) : ¬ (e = c ∧ f = d) := D.2.2.2.2.2.2.2.2.1

theorem DomS.k4 {a b c d e f : Nat} (D : DomS a b c d e f) :
    ¬ (f = d + 1 ∧ (e = c + 1 ∨ e + 1 = c)) := D.2

theorem WeakStep.k5 {a b c d e f x y : Nat} (s : WeakStep a b c d e f x y) : ¬ (e = x ∧ f = y) :=
  s.1.2.2.2.2

theorem WeakStep.k6 {a b c d e f x y : Nat} (s : WeakStep a b c d e f x y) : ¬ (x = c ∧ y = d) :=
  s.2.2.2.1

theorem WeakStep.k7 {a b c d e f x y : Nat} (s : WeakStep a b c d e f x y) :
    a + 2 ≤ x ∨ x + 2 ≤ a ∨ b + 2 ≤ y ∨ y + 2 ≤ b := s.2.2.2.2.1

theorem WeakStep.k8 {a b c d e f x y : Nat} (s : WeakStep a b c d e f x y) :
    ¬ (y = d + 1 ∧ (x = c + 1 ∨ x + 1 = c)) := s.2.2.2.2.2

theorem KingStep.k5 {a b c d e f x y : Nat} (s : KingStep a b c d e f x y) : ¬ (a = x ∧ b = y) :=
  s.1.2.2.2.2

theorem KingStep.k6 {a b c d e f x y : Nat} (s : KingStep a b c d e f x y) : ¬ (x = c ∧ y = d) :=
  s.2.2.2.1

theorem KingStep.k7 {a b c d e f x y : Nat} (s : KingStep a b c d e f x y) :
    x + 2 ≤ e ∨ e + 2 ≤ x ∨ y + 2 ≤ f ∨ f + 2 ≤ y := s.2.2.2.2

end EndgameChess.Rules.KPK.Coord
