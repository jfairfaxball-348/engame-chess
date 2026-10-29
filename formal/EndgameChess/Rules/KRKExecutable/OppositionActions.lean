import EndgameChess.Rules.KRKExecutable.ColumnKing
import EndgameChess.Rules.KRKForcing.TwoFileCheck
import EndgameChess.Rules.KRKForcing.CheckProgress

/-!
Concrete two-file opposition check and its explicit king-up continuation.
The frozen source proves mate immediately at the edge, or an actual four-ply
strictly decreasing barrier-height step against every defender continuation.
This module does not provide a complete global setup/phase dispatcher.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules

def oppositionCheckDestination (rs wk : Square) : Square := checkRook rs wk

theorem oppositionCheck_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (ho : Opposed sk wk)
    (hf : 2≤absDiff rs.1.val wk.1.val)
    (hy : rs.2.val≠wk.2.val) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨sk,oppositionCheckDestination rs wk,wk,false⟩ ∧
      (MateGoal σ c ∨
        ((∃ r, Legal c r) ∧ ∀ r, Legal c r →
          ∃ t, Matches r σ ⟨sk,oppositionCheckDestination rs wk,t,true⟩ ∧
            t.2.val=wk.2.val+1 ∧ absDiff t.1.val wk.1.val≤1)) := by
  simpa only [oppositionCheckDestination] using
    krk_opposition_check_two hq ho hf hy

def oppositionFollowDestination (sk : Square)
    (h : sk.2.val<7) : Square :=
  (sk.1,⟨sk.2.val+1,by omega⟩)

/-- This exact next king step, after *any* defender reply to the check,
has a legal move, nonempty defender replies, and produces an oriented
distant barrier with strictly lower weak-king upper-height potential. -/
theorem oppositionFollow_sound {q : Position} {σ : Colour}
    {sk rs wk t : Square}
    (hq : Matches q σ ⟨sk,rs,t,true⟩)
    (ho : Opposed sk wk)
    (hf : 4≤absDiff rs.1.val wk.1.val)
    (hy : rs.2.val=wk.2.val)
    (hty : t.2.val=wk.2.val+1)
    (htx : absDiff t.1.val wk.1.val≤1) :
    ∃ u, Legal q u ∧
      Matches u σ ⟨oppositionFollowDestination sk (by omega),rs,t,false⟩ ∧
      (∃ v, Legal u v) ∧ ∀ v, Legal u v →
        ∃ w, Matches v σ ⟨oppositionFollowDestination sk (by omega),rs,w,true⟩ ∧
          DistantBarrier (oppositionFollowDestination sk (by omega)) rs w ∧
          7-w.2.val<7-wk.2.val := by
  obtain ⟨su,u,hsx,hsy,hl,hmu,hne,hall⟩ :=
    krk_follow_check hq ho hf hy hty htx
  have heq : su=oppositionFollowDestination sk (by omega) := by
    apply Prod.ext
    · apply Fin.ext
      exact hsx
    · apply Fin.ext
      exact hsy
  rw [heq] at hmu hall
  exact ⟨u,hl,hmu,hne,hall⟩

end EndgameChess.Rules.KRKExecutable
