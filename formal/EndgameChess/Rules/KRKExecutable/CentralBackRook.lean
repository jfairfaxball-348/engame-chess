import EndgameChess.Rules.KRKExecutable.CentralAlignedRescue
import EndgameChess.Rules.KRKCentral.Positive
import EndgameChess.Rules.KRKExecutable.LowerPursuitPair

/-!
KRK06: exact low-rook-margin orientation action used by the fallback
of KRKCentral.positive_bound. This is a local first pair, not a
certification of the recursive Back/BackEven continuation.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules EndgameChess.Rules.KRKCentral

def centralBackDestination (d : Bool) (rs : Square) : Square :=
  backRook d (if pursuitFile d rs=0 then 1 else 0) rs

/-- Under an oriented central wall, moving the rook to the extreme
back file (or the adjacent file if already there) is a constructive
legal move. All weak replies preserve the rank wall and >=2 rook
files of separation. This specialises the non-chase branch of
KRKCentral.positive_bound, with no global strategy claim. -/
theorem centralBackRook_sound (d : Bool) {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val)
    (hwy : rs.2.val<wk.2.val)
    (hs : 3≤pursuitFile d sk)
    (hw : pursuitFile d sk<pursuitFile d wk) :
    let nr := centralBackDestination d rs
    ∃ c, Legal q c ∧ Matches c σ ⟨sk,nr,wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk,nr,t,true⟩ ∧
          rs.2.val<t.2.val ∧ 2≤absDiff nr.1.val t.1.val := by
  dsimp
  let k : Fin 8 := if pursuitFile d rs=0 then 1 else 0
  let nr : Square := backRook d k rs
  have hnr : pursuitFile d nr=k.val := by
    cases d <;> simp [nr,backRook,backFile,pursuitFile] <;> omega
  have hk : k.val≤1 := by dsimp [k]; split <;> decide
  have hdistinct : nr≠rs := by
    intro he
    have hsame : pursuitFile d nr=pursuitFile d rs :=
      congrArg (pursuitFile d) he
    dsimp [k] at hnr
    split at hnr <;> simp only [Fin.val_zero,Fin.val_one] at hnr <;> omega
  have hf3 : 3≤absDiff nr.1.val wk.1.val := by
    rw [←pursuit_absDiff d nr wk]
    simp only [absDiff]
    omega
  obtain ⟨c,hl,hm,hne,hall⟩ :=
    krk_wall_rook_move hq (by omega) hwy
      (nr := nr) rfl hdistinct hf3
  refine ⟨c,hl,hm,hne,?_⟩
  intro v hv
  obtain ⟨t,hmt,hty,hft,_,_⟩ := hall v hv
  exact ⟨t,hmt,hty,hft⟩

#print axioms EndgameChess.Rules.KRKExecutable.centralBackRook_sound

end EndgameChess.Rules.KRKExecutable
