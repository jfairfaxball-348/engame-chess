import EndgameChess.Rules.KRKExecutable.WidePivot
import EndgameChess.Rules.KRKCentral.Guarded

/-!
Explicit first king step of the frozen guarded NE continuation.
The proof certifies every actual weak reply stays within the perpendicular
cut. The resulting axis-swapped column-wall strategy remains unextracted;
this module is NOT a total mate policy or a new mate bound.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

/-- A king on the lower-left diagonal steps onto the rook's rank and
becomes horizontally adjacent to the rook. -/
def guardedEntryDestination (sk rs : Square) : Square := (sk.1,rs.2)

/-- Concrete legally played king step and **universal** weak reply region:
the weak king remains strictly above and right of the rook. -/
theorem guardedEntry_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsx : sk.1.val+1=rs.1.val)
    (hsy : sk.2.val+1=rs.2.val)
    (hwx : rs.1.val<wk.1.val)
    (hwy : rs.2.val<wk.2.val)
    (ha : 3≤rs.1.val) (ha5 : rs.1.val≤5) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨guardedEntryDestination sk rs,rs,wk,false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨guardedEntryDestination sk rs,rs,t,true⟩ ∧
          rs.1.val<t.1.val ∧ rs.2.val<t.2.val := by
  let su : Square := guardedEntryDestination sk rs
  have hstep : StepM ⟨sk,rs,wk,true⟩ ⟨su,rs,wk,false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;>
      simp only [su,guardedEntryDestination,dInf,absDiff,ne_iff_coords] at * <;> omega
  obtain ⟨c,hl,hm⟩ := step_sound hq hstep
  let tx : Fin 8 := if h : wk.1.val=7 then 6 else ⟨wk.1.val+1,by omega⟩
  let tt : Square := (tx,wk.2)
  have ht : StepM ⟨su,rs,wk,false⟩ ⟨su,rs,tt,true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [su,guardedEntryDestination,tt,tx,dInf,absDiff,
        ne_iff_coords,RookSees,RookLine,OnSeg] at * <;>
      split <;> (try dsimp only at *) <;> omega
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  refine ⟨c,hl,hm,⟨v,hv⟩,?_⟩
  intro z hz
  have hsafe : SafeRook su rs wk := Or.inr (by
    simp only [su,guardedEntryDestination,dInf,absDiff] at *; omega)
  obtain ⟨t,hmt,hst⟩ := krk_safe_reply (sk := su) (rs := rs) (wk := wk)
    hm.1 hm.2 hsafe hz
  have hregion : rs.1.val<t.1.val ∧ rs.2.val<t.2.val := by
    cases hst with
    | lone hd hn hf hsee =>
      simp only [su,guardedEntryDestination,dInf,absDiff,
        ne_iff_coords,RookSees,RookLine,OnSeg] at *
      omega
  exact ⟨t,hmt,hregion.1,hregion.2⟩

/-- Mirrored guarded first king step, on a rook at file 2..4 with
a weaker king to its left. This explicitly extracts the left counterpart
of KRKCentral.guarded_bound's transported construction. -/
theorem guardedEntryLeft_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsx : rs.1.val+1=sk.1.val)
    (hsy : sk.2.val+1=rs.2.val)
    (hwx : wk.1.val<rs.1.val)
    (hwy : rs.2.val<wk.2.val)
    (ha : 2≤rs.1.val) (ha4 : rs.1.val≤4) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨guardedEntryDestination sk rs,rs,wk,false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨guardedEntryDestination sk rs,rs,t,true⟩ ∧
          t.1.val<rs.1.val ∧ rs.2.val<t.2.val := by
  let su : Square := guardedEntryDestination sk rs
  have hstep : StepM ⟨sk,rs,wk,true⟩ ⟨su,rs,wk,false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;>
      simp only [su,guardedEntryDestination,dInf,absDiff,ne_iff_coords] at * <;> omega
  obtain ⟨c,hl,hm⟩ := step_sound hq hstep
  let tx : Fin 8 := if h : wk.1.val=0 then 1 else ⟨wk.1.val-1,by omega⟩
  let tt : Square := (tx,wk.2)
  have ht : StepM ⟨su,rs,wk,false⟩ ⟨su,rs,tt,true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [su,guardedEntryDestination,tt,tx,dInf,absDiff,
        ne_iff_coords,RookSees,RookLine,OnSeg] at * <;>
      split <;> (try dsimp only at *) <;> omega
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  refine ⟨c,hl,hm,⟨v,hv⟩,?_⟩
  intro z hz
  have hsafe : SafeRook su rs wk := Or.inr (by
    simp only [su,guardedEntryDestination,dInf,absDiff] at *; omega)
  obtain ⟨t,hmt,hst⟩ := krk_safe_reply (sk := su) (rs := rs) (wk := wk)
    hm.1 hm.2 hsafe hz
  have hregion : t.1.val<rs.1.val ∧ rs.2.val<t.2.val := by
    cases hst with
    | lone hd hn hf hsee =>
      simp only [su,guardedEntryDestination,dInf,absDiff,
        ne_iff_coords,RookSees,RookLine,OnSeg] at *
      omega
  exact ⟨t,hmt,hregion.1,hregion.2⟩

end EndgameChess.Rules.KRKExecutable
