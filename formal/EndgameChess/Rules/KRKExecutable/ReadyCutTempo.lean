import EndgameChess.Rules.KRKExecutable.WallClimb
import EndgameChess.Rules.KRKCentral.ReadyCut

/-!
A strictly scoped, computable piece of the READY lower-band branch. In the
unaligned narrow-file case, the original ready_cut_bound proof executes a
concrete rook tempo before entering an exit/alignment/pivot continuation.
This file extracts and checks that *one* chosen move and all legal replies.
It does NOT constitute a total game-winning selector or mate budget.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

/-- The actual rook-tempo coordinate used in ReadyCut's narrow-band branch. -/
def lowerBandTempoDestination (rs wk : Square) : Square :=
  rookWaitDestination rs wk

/-- For the narrow, unaligned READY band, this deterministic legal rook move
retains a safe wall and maps *every* legal defender reply to either an
upper-band exit, a same-file alignment, or a wide-file pivot. This theorem
certifies exactly the handoff cases; their further strategies are not yet
executable here. -/
theorem lowerBandTempo_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val)
    (hwy : wk.2.val=rs.2.val+1)
    (_hcentre : sk.1.val=3 ∨ sk.1.val=4)
    (_hmargin : 2≤absDiff rs.1.val wk.1.val)
    (_hunaligned : sk.1.val≠wk.1.val)
    (_hnarrow : ¬ (2≤absDiff sk.1.val wk.1.val)) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨sk,lowerBandTempoDestination rs wk,wk,false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk,lowerBandTempoDestination rs wk,t,true⟩ ∧
          2≤absDiff (lowerBandTempoDestination rs wk).1.val t.1.val ∧
          (rs.2.val+2≤t.2.val ∨
           sk.1.val=t.1.val ∨
           2≤absDiff sk.1.val t.1.val) := by
  let nr : Square := lowerBandTempoDestination rs wk
  have hchoice := wall_wait_choice rs.1 wk.1
  have hdistinct : nr≠rs := by
    intro he
    apply hchoice.1
    exact congrArg Prod.fst he
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
    (nr := nr) rfl hdistinct hchoice.2
  refine ⟨c,hl,hm,hne,?_⟩
  intro v hv
  obtain ⟨t,hmt,_,hft,hunit,hshape⟩ := hall v hv
  have hcases : rs.2.val+2≤t.2.val ∨
      sk.1.val=t.1.val ∨ 2≤absDiff sk.1.val t.1.val := by
    rcases hshape hwy with hu | ⟨htband,hdx⟩
    · exact Or.inl hu
    · by_cases ha : sk.1.val=t.1.val
      · exact Or.inr (Or.inl ha)
      · have hw : 2≤absDiff sk.1.val t.1.val := by
          simp only [absDiff] at *
          omega
        exact Or.inr (Or.inr hw)
  exact ⟨t,hmt,hft,hcases⟩

end EndgameChess.Rules.KRKExecutable
