import EndgameChess.Rules.KRKExecutable.RestorationFirst

/-!
KRK05: second, exact centre-alignment king step used by the original
KRKCentral.restoration_bound catch-up proof. A post-catch-up king on file
2 or 5 can move one file to 3 or 4 while keeping the rook-rank wall.
This is still a local proof and does not certify an entire mating policy.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules

def restorationCentreDestination (sk : Square) : Square :=
  (if sk.1.val < 3 then ⟨3,by decide⟩ else ⟨4,by decide⟩,sk.2)

/-- The second catch-up move is chosen by a coordinate calculation,
with quantified all-defender wall preservation and central king file. -/
theorem restorationCentre_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val<rs.2.val)
    (hw : rs.2.val<wk.2.val)
    (hx : sk.1.val=2 ∨ sk.1.val=5)
    (hf : 2≤absDiff rs.1.val wk.1.val) :
    let su := restorationCentreDestination sk
    ∃ c, Legal q c ∧ Matches c σ ⟨su,rs,wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨su,rs,t,true⟩ ∧
          rs.2.val<t.2.val ∧
          (su.1.val=3 ∨ su.1.val=4) := by
  dsimp
  let su : Square := restorationCentreDestination sk
  have hcentre : su.1.val=3 ∨ su.1.val=4 := by
    dsimp [su,restorationCentreDestination]
    split <;> simp
  have hstep : dInf sk su=1 := by
    rcases hx with hx | hx
    · dsimp [su,restorationCentreDestination]
      simp [hx,dInf,absDiff]
    · dsimp [su,restorationCentreDestination]
      simp [hx,dInf,absDiff]
  obtain ⟨c,hl,hm,hnonempty,hall⟩ :=
    king_below_pair hq hstep hb hw hf
  refine ⟨c,hl,hm,hnonempty,?_⟩
  intro v hv
  obtain ⟨t,hmt,hty,_⟩ := hall v hv
  exact ⟨t,hmt,hty,hcentre⟩

end EndgameChess.Rules.KRKExecutable
