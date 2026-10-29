import EndgameChess.Rules.KRKExecutable.GuardedEntry
import EndgameChess.Rules.KRKCentral.Column

/-!
Column-wall entry, the exact interior strong-king horizontal approach used
in the frozen Column.column_bound proof. Full 16-ply column strategy still
needs the second central step, exit and restoration branches.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

/-- The nearest one-file step toward central files 3 or 4, with the original
king rank unchanged. Only used for an interior noncentral strong king. -/
def columnKingDestination (sk : Square)
    (h : (sk.1.val=1 ∨ sk.1.val=2) ∨
         (sk.1.val=5 ∨ sk.1.val=6)) : Square :=
  (⟨if sk.1.val<3 then sk.1.val+1 else sk.1.val-1, by omega⟩,sk.2)

/-- A computable first step toward the centre under the precise distant
column-wall precondition. Every legal defender move leaves a strict wall,
a file margin >=2 and the new strong king within files 2..5. -/
theorem columnKingStep_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val<rs.2.val) (hw : rs.2.val<wk.2.val)
    (hmargin : 3≤absDiff rs.1.val wk.1.val)
    (hin : (sk.1.val=1 ∨ sk.1.val=2) ∨
           (sk.1.val=5 ∨ sk.1.val=6)) :
    let su := columnKingDestination sk hin
    ∃ c, Legal q c ∧ Matches c σ ⟨su,rs,wk,false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨su,rs,t,true⟩ ∧
          rs.2.val<t.2.val ∧ 2≤absDiff rs.1.val t.1.val ∧
          2≤su.1.val ∧ su.1.val≤5 := by
  dsimp
  let su := columnKingDestination sk hin
  have hsux : 2≤su.1.val ∧ su.1.val≤5 ∧
       absDiff sk.1.val su.1.val=1 := by
    simp only [su,columnKingDestination,absDiff]
    split <;> omega
  have hstep : dInf sk su=1 := by
    change max (absDiff sk.1.val su.1.val)
      (absDiff sk.2.val su.2.val)=1
    simp only [su,columnKingDestination,absDiff] at *
    split <;> omega
  obtain ⟨c,hl,hm,hne,hall⟩ :=
    king_below_pair hq hstep hb hw hmargin
  refine ⟨c,hl,hm,hne,?_⟩
  intro v hv
  obtain ⟨t,hmt,hty,hunit⟩ := hall v hv
  have hft : 2≤absDiff rs.1.val t.1.val := by
    simp only [absDiff] at *
    omega
  exact ⟨t,hmt,hty,hft,hsux.1,hsux.2.1⟩

end EndgameChess.Rules.KRKExecutable
