import EndgameChess.Rules.KRKExecutable.ReadyCutTempo
import EndgameChess.Rules.KRKCentral.Pivot
import EndgameChess.Rules.KRKBox.Region

/-!
Executable first **protected perpendicular rook cut** for the right-oriented
wide READY lower band. This is precisely the constructive case of the frozen
KRKCentral.Pivot.pivot_right proof, but with a computable coordinate and an
all-defence successor-region certificate. A rook already on the target file
is a GUARDED HANDOFF, not an illegal no-op. This does not extract the guarded
continuation or prove a global executable KRK player.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

/-- In the right-oriented wide lower band, choose the rook square one file to
the right of the strong king, on the rook's current rank. -/
def pivotRightDestination (sk rs : Square)
    (h : sk.1.val < 7) : Square :=
  (⟨sk.1.val+1, by omega⟩,rs.2)

/-- Either the rook already occupies the guarded destination (handoff),
or the exact rook move is legal, has a nonempty weak reply set, and *every*
defender reply lies to the right of its protected vertical cut. -/
theorem pivotRightCut_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val)
    (hwy : wk.2.val=rs.2.val+1)
    (hs : sk.1.val=3 ∨ sk.1.val=4)
    (hx : sk.1.val+2≤wk.1.val) :
    let nr := pivotRightDestination sk rs (by omega)
    nr = rs ∨
    (∃ c, Legal q c ∧ Matches c σ ⟨sk,nr,wk,false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk,nr,t,true⟩ ∧
          nr.1.val < t.1.val ∧ nr.2.val < t.2.val ∧
          dInf sk nr = 1) := by
  dsimp
  let nr : Square := pivotRightDestination sk rs (by omega)
  have hnrx : nr.1.val = sk.1.val+1 := rfl
  have hnry : nr.2 = rs.2 := rfl
  by_cases he : nr=rs
  · exact Or.inl he
  right
  have hs2 : StepM ⟨sk,rs,wk,true⟩ ⟨sk,nr,wk,false⟩ := by
    refine StepM.rook ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [nr,pivotRightDestination,RookLine,OnSeg,ne_iff_coords,
        dInf,absDiff,and_true,or_true] at * <;> omega
  obtain ⟨c,hl,hm⟩ := step_sound hq hs2
  obtain ⟨t,ht⟩ := krk_box_reply_exists (sk := sk) (rs := nr) (wk := wk)
    (lo := nr.1.val+1) (hi := 7) (by change sk.2.val+1=rs.2.val; exact hsy)
    (by change rs.2.val<wk.2.val; omega) (by omega) (by omega)
    (Or.inl (by omega)) (by omega) (by omega)
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  refine ⟨c,hl,hm,⟨v,hv⟩,?_⟩
  intro z hz
  obtain ⟨t,hmt,hty,hunit,hxt⟩ := krk_box_reply_region hm
    (by change sk.2.val+1=rs.2.val; exact hsy)
    (by change rs.2.val<wk.2.val; omega)
    (by simp only [nr,pivotRightDestination,dInf,absDiff]; omega) hz
  have hwxt : nr.1.val<t.1.val := by
    simp only [absDiff] at hunit
    dsimp [nr,pivotRightDestination] at *
    omega
  exact ⟨t,hmt,hwxt,hty,by simp only [nr,pivotRightDestination,dInf,absDiff]; omega⟩

end EndgameChess.Rules.KRKExecutable
