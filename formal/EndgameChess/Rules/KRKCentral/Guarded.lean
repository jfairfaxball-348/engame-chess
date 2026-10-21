import EndgameChess.Rules.KRKCentral.ColumnWall
import EndgameChess.Rules.KRKForcing.AxisWalls

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- The guarded NE continuation for widths2..4. The initial king-up pair
is nonstalemating because the weak file interval has at least two squares.
The axis-swapped close wall uses only the already proved uncut central tail. -/
theorem guarded_bound {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsx : sk.1.val+1=rs.1.val) (hsy : sk.2.val+1=rs.2.val)
    (hwx : rs.1.val<wk.1.val) (hwy : rs.2.val<wk.2.val)
    (ha : 3≤rs.1.val) (ha5 : rs.1.val≤5) :
    MateWithin σ (18*(7-rs.1.val)+1) q := by
  let su : Square := (sk.1,rs.2)
  have hstep : StepM ⟨sk,rs,wk,true⟩ ⟨su,rs,wk,false⟩ := by
    refine StepM.king ?_ ?_ ?_ <;>
      simp only [su,dInf,absDiff,ne_iff_coords] at * <;> omega
  obtain ⟨c,hl,hm⟩ := step_sound hq hstep
  let tx : Fin 8 := if h : wk.1.val=7 then 6 else ⟨wk.1.val+1,by omega⟩
  let tt : Square := (tx,wk.2)
  have ht : StepM ⟨su,rs,wk,false⟩ ⟨su,rs,tt,true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [su,tt,tx,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg] at * <;>
      split <;> (try dsimp only at *) <;> omega
  obtain ⟨v,hv,_⟩ := step_sound hm ht
  apply mateWithin_mono (n := (18*(7-rs.1.val)-1)+2) ?_ (by omega)
  apply mateWithin_pair (σ := σ) hq.2 hl hm.2 ⟨v,hv⟩
  intro z hz
  have hsafe : SafeRook su rs wk := Or.inr (by
    simp only [su,dInf,absDiff] at *; omega)
  obtain ⟨t,hmt,hst⟩ := krk_safe_reply (sk := su) (rs := rs) (wk := wk) hm.1 hm.2 hsafe hz
  have hregion : rs.1.val<t.1.val ∧ rs.2.val<t.2.val := by
    cases hst with
    | lone hd hn hf hsee =>
      simp only [su,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg] at *
      omega
  have hcanon : Matches (krkPos σ (symSwap.f su) (symSwap.f rs) (symSwap.f t) σ) σ
      ((⟨su,rs,t,true⟩ : KRKState).map symSwap) :=
    ⟨⟨symSwap.ne_iff.2 hmt.1.1,symSwap.ne_iff.2 hmt.1.2.1,
      symSwap.ne_iff.2 hmt.1.2.2.1,rfl⟩,rfl⟩
  apply krk_bound_transport symSwap hcanon rfl
  · simpa only [KRKState.map_map] using hmt
  · exact column_wall_bound hcanon (by change sk.1.val+1=rs.1.val; exact hsx)
      hregion.1 (by change 1≤rs.2.val; omega) (by change rs.2.val≤6; omega)

end EndgameChess.Rules.KRKCentral
