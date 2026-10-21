import EndgameChess.Rules.KRKForcing.Safety

/-! EC-C051: finite actual all-reply KRK phases. No history symmetry or mate
claim is built into the endpoint predicate. A pair costs two board plies. -/
namespace EndgameChess.Rules
open EndgameChess.KK

inductive KRKBoxPhase (σ : Colour) (Q : Position → Prop) : Nat → Position → Prop
  | done {n q} : Q q → KRKBoxPhase σ Q n q
  | pair {n q c} : q.turn = σ → Legal q c → c.turn = σ.opp →
      (∃ r, Legal c r) → (∀ r, Legal c r → KRKBoxPhase σ Q n r) →
      KRKBoxPhase σ Q (n+1) q

def boxExcess (w h : Nat) : Nat := (w-4) + (h-4)

def BoxCorner (σ : Colour) (a b : Nat) (q : Position) : Prop :=
  ∃ sk rs wk : Square, Matches q σ ⟨sk,rs,wk,true⟩ ∧
    rs.1.val = a+1 ∧ rs.2.val = b ∧ sk.2.val+1 = b ∧ b < wk.2.val ∧
    ((sk.1.val = a ∧ a+1 < wk.1.val) ∨
     (sk.1.val = a+2 ∧ wk.1.val < a+1))

end EndgameChess.Rules
