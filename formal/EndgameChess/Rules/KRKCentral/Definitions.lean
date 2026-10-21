import EndgameChess.Rules.KRKBound.Pair
import EndgameChess.Rules.KRKForcing.TwoFileCheck
import EndgameChess.Rules.KRKBound.Transport

/-! EC-C052: only the phase predicates needed by the whole wall95 proof. -/
namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK

def Exit (σ : Colour) (y : Nat) (q : Position) : Prop :=
  ∃ sk rs wk : Square, Matches q σ ⟨sk,rs,wk,true⟩ ∧
    sk.2.val+1=y ∧ rs.2.val=y ∧ y<wk.2.val ∧
    1≤sk.1.val ∧ sk.1.val≤6 ∧ 2≤absDiff rs.1.val wk.1.val ∧
    (y+2≤wk.2.val ∨ sk.1.val=wk.1.val)

def ExitBound (σ : Colour) (y E : Nat) : Prop :=
  ∀ q, Exit σ y q → MateWithin σ E q

def CentralBound (σ : Colour) (y E : Nat) : Prop :=
  ∀ {q : Position} {sk rs wk : Square}, Matches q σ ⟨sk,rs,wk,true⟩ →
    sk.2.val+1=y → rs.2.val=y → y<wk.2.val →
    (sk.1.val=3 ∨ sk.1.val=4) → MateWithin σ E q

def backFile (d : Bool) (k : Fin 8) : Fin 8 :=
  if d then k else ⟨7-k.val, by omega⟩

def backRook (d : Bool) (k : Fin 8) (rs : Square) : Square :=
  (backFile d k,rs.2)

end EndgameChess.Rules.KRKCentral
