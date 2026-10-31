import EndgameChess.Rules.KPK.Coord.Hold
import EndgameChess.Rules.KPK.Coord.Replies

/-! The draws with a pawn on the seventh rank. The lone king stands on the promotion
square, and the strong king cannot arrive next to the pawn on a side square with the
lone king to move; or it stands beside the pawn and the strong king cannot reach the
far side of the promotion square. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- One step from `(x,y)`, or on it when `Near` is widened by equality. -/
def Within1 (a b x y : Nat) : Prop := a ≤ x + 1 ∧ x ≤ a + 1 ∧ b ≤ y + 1 ∧ y ≤ b + 1

/-- Blockade on the promotion square. -/
def Block7 (a b c e f : Nat) : Prop :=
  e = c ∧ f = 7 ∧ ¬ Near a b (c + 1) 5 ∧ ¬ (1 ≤ c ∧ Near a b (c - 1) 5)

/-- Beside the pawn on the left, the strong king too far from the right of the
promotion square. -/
def SideL (a b c e f : Nat) : Prop :=
  e + 1 = c ∧ f = 6 ∧ ¬ Within1 a b (c + 1) 6 ∧ ¬ Within1 a b (c + 1) 7

/-- Beside the pawn on the right, mirrored. -/
def SideR (a b c e f : Nat) : Prop :=
  e = c + 1 ∧ f = 6 ∧ ¬ Within1 a b (c - 1) 6 ∧ ¬ Within1 a b (c - 1) 7

def TS (a b c d e f : Nat) : Prop :=
  1 ≤ c ∧ d = 6 ∧ (Block7 a b c e f ∨ SideL a b c e f ∨ SideR a b c e f)

/-- The lone king answers: it takes the pawn, is stalemated, or returns to the region. -/
def TW (a b c d e f : Nat) : Prop :=
  Capture a b c d e f ∨ (∀ x y, ¬ WeakStep a b c d e f x y) ∨
    ∃ x y, WeakStep a b c d e f x y ∧ TS a b c d x y

theorem top_capture {c e f x y : Nat} (near : Near e f c 6) (far : ¬ Near x y c 6) :
    TW x y c 6 e f := Or.inl ⟨near, far⟩

/-- King below the pawn with the lone king on the promotion square: no move at all. -/
theorem top_stale (c : Nat) : TW c 5 c 6 c 7 := by
  refine Or.inr (Or.inl fun x y s => ?_)
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds s
  have k5 := s.k5
  have k6 := s.k6
  have k7 := s.k7
  have k8 := s.k8
  omega

set_option maxHeartbeats 4000000 in
/-- The top guard. -/
def topGuard : Guard where
  S := TS
  W := TW
  strong := by
    intro a b c d e f D h
    obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
    have k1 := D.1.k1
    have k2 := D.1.k2
    obtain ⟨hc, rfl, h⟩ := h
    refine ⟨?_, fun _ q => by omega, fun q => by omega, ?_⟩
    · intro x y st
      obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := KingStep.bounds st
      have s1 := st.1
      have s2 := st.k6
      have s3 := st.k7
      rcases h with ⟨rfl, rfl, q1, q2⟩ | ⟨he, rfl, q1, q2⟩ | ⟨he, rfl, q1, q2⟩
      · by_cases near : Near x y e 6
        · unfold Near at near s1 q1 q2
          by_cases mid : x = e
          · have : y = 5 := by omega
            subst mid; subst this
            exact top_stale x
          · omega
        · exact top_capture (by unfold Near; omega) near
      · by_cases near : Near x y c 6
        · unfold Near at near s1
          unfold Within1 at q1 q2
          have hx : x = c + 1 ∧ y = 5 := by omega
          obtain ⟨hx, rfl⟩ := hx
          subst hx
          refine Or.inr (Or.inr ⟨c, 7, ?_, hc, rfl, Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩)
          · unfold WeakStep Near Apart Att; omega
          · unfold Near; omega
          · unfold Near; omega
        · exact top_capture (by unfold Near; omega) near
      · by_cases near : Near x y c 6
        · unfold Near at near s1
          unfold Within1 at q1 q2
          have hx : x + 1 = c ∧ y = 5 := by omega
          obtain ⟨hx, rfl⟩ := hx
          refine Or.inr (Or.inr ⟨c, 7, ?_, hc, rfl, Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩)
          · unfold WeakStep Near Apart Att; omega
          · unfold Near; omega
          · unfold Near; omega
        · exact top_capture (by unfold Near; omega) near
    · intro _ fr
      unfold Free at fr
      rcases h with ⟨he, rfl, q1, q2⟩ | ⟨he, rfl, q1, q2⟩ | ⟨he, rfl, q1, q2⟩
      · omega
      · unfold Within1 at q1 q2
        constructor <;> unfold Near <;> omega
      · unfold Within1 at q1 q2
        constructor <;> unfold Near <;> omega
  weak := by
    intro a b c d e f _ h
    exact h

/-- Pawn on the seventh, a fresh root in the top guard: the lone king holds. -/
theorem fresh_top_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (sat : SD topGuard σ sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong h fresh turn safe sat

end EndgameChess.Rules.KPK.Coord
