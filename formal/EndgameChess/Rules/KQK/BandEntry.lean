import EndgameChess.Rules.KQK.BandForce

/-! Prepare an arbitrary king below a separating rank, without disturbing
the queen wall. The resulting cost is bounded jointly with the drive. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def preparationPotential (sk qs : Square) : Nat :=
  qs.2.val-1-sk.2.val+absDiff sk.1.val qs.1.val

def wallBudget (sk qs : Square) : Nat :=
  2*preparationPotential sk qs+4*(7-qs.1.val)+4*(5-qs.2.val)+33

private theorem preparation_step {sk qs : Square} (below : sk.2.val < qs.2.val)
    (notReady : ¬ (sk.1.val = qs.1.val ∧ sk.2.val+1 = qs.2.val)) :
    ∃ su : Square, dInf sk su = 1 ∧ su.2.val < qs.2.val ∧
      preparationPotential su qs+1 = preparationPotential sk qs := by
  by_cases vertical : sk.2.val+1 < qs.2.val
  · let su : Square := (sk.1,⟨sk.2.val+1,by have bound := qs.2.isLt; omega⟩)
    exact ⟨su,by simp only [dInf,absDiff,su]; omega,by dsimp [su]; omega,
      by simp only [preparationPotential,su]; omega⟩
  · have rank : sk.2.val+1 = qs.2.val := by omega
    have different : sk.1.val ≠ qs.1.val := by omega
    let x : Fin 8 := ⟨if sk.1.val < qs.1.val then sk.1.val+1 else sk.1.val-1,by
      have bx := sk.1.isLt
      have qx := qs.1.isLt
      split <;> omega⟩
    let su : Square := (x,sk.2)
    refine ⟨su,?_,below,?_⟩
    · dsimp [dInf,absDiff,su,x]; split <;> omega
    · dsimp [preparationPotential,absDiff,su,x]; split <;> omega

/-- Fixed-wall king preparation, charged together with the remaining
prepared-wall potential rather than by adding independent worst cases. -/
theorem wall_prepare_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (wall : Wall sk qs wk) (band : OpenBand qs) (hc : inCheck q σ.opp = false) :
    MateWithin σ (wallBudget sk qs) q := by
  generalize hpot : preparationPotential sk qs = p
  induction p using Nat.strongRecOn generalizing q sk wk with
  | ind p ih =>
    by_cases ready : sk.1.val = qs.1.val ∧ sk.2.val+1 = qs.2.val
    · have top : qs.2.val ≤ 5 := by rcases band with low | ⟨five,_⟩ <;> omega
      have hp : Prepared sk qs wk := ⟨wall,top,ready.2,by omega,by have := wall.2.2; omega⟩
      have win := prepared_bound hq ht hp hc
      exact mateWithin_mono win (by simp only [wallBudget,bandPotential]; omega)
    · obtain ⟨su,step,below,decrease⟩ := preparation_step wall.1 ready
      have above := wall.2.1
      obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht step
        (by simp only [ne_iff_coords]; omega)
        (by simp only [dInf,absDiff]; omega)
      have next : Wall su qs wk := ⟨below,wall.2⟩
      have safe : SafeQueen su qs wk := Or.inl (queen_distant_of_not_check hq hc)
      have result : MateWithin σ (wallBudget su qs+2) q := by
        apply mateWithin_pair ht hl hct (wall_reply_exists hm hct next band)
        intro r hr
        obtain ⟨t,hmt,hrt,wallt,_,_,notCheck⟩ := wall_reply hm hct next safe hr
        exact ih (preparationPotential su qs) (by omega) hmt hrt wallt notCheck rfl
      exact mateWithin_mono result (by simp only [wallBudget]; omega)

theorem wall_band_ninety_one {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (wall : Wall sk qs wk) (band : OpenBand qs) (hc : inCheck q σ.opp = false) :
    MateWithin σ 91 q := by
  have top : qs.2.val ≤ 5 := by rcases band with low | ⟨five,_⟩ <;> omega
  have below := wall.1
  have bx := sk.1.isLt
  have bound : wallBudget sk qs ≤ 91 := by
    simp only [wallBudget,preparationPotential,absDiff]
    omega
  exact mateWithin_mono (wall_prepare_bound hq ht wall band hc) (by omega)

/-- Every strict upper-right separating wall is covered, including queen
rank six and the narrow rank-five corner trap. -/
theorem wall_ninety_one {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (wall : Wall sk qs wk) (hc : inCheck q σ.opp = false) : MateWithin σ 91 q := by
  obtain ⟨below,above,right⟩ := wall
  have wxBound := wk.1.isLt
  have wyBound := wk.2.isLt
  have distant := queen_distant_of_not_check hq hc
  by_cases top : qs.2.val = 6
  · have wy : wk.2.val = 7 := by omega
    have gap : qs.1.val+2 ≤ wk.1.val := by simp only [dInf,absDiff] at distant; omega
    by_cases wide : qs.1.val ≤ 4
    · exact mateWithin_mono (edge_wall_twenty_five hq ht ⟨by omega,top,wy,wide,gap⟩) (by decide)
    · have qx : qs.1.val = 5 := by omega
      let nq : Square := (4,6)
      obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht
        (near_sees (by simp only [dInf,absDiff,nq]; omega))
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [dInf,absDiff]; omega)
      exact mateWithin_mono (mateWithin_choose ht hl (edge_wall_weak_bound hm hct
        ⟨by omega,rfl,wy,by decide,by dsimp [nq]; omega⟩)) (by decide)
  have low : qs.2.val ≤ 5 := by omega
  by_cases band : OpenBand qs
  · exact wall_band_ninety_one hq ht ⟨below,above,right⟩ band hc
  have qy : qs.2.val = 5 := by
    by_cases lower : qs.2.val ≤ 4
    · exact False.elim (band (Or.inl lower))
    · omega
  have qx : qs.1.val = 6 := by
    by_cases left : qs.1.val ≤ 5
    · exact False.elim (band (Or.inr ⟨qy,left⟩))
    · omega
  have wx : wk.1.val = 7 := by omega
  have wy : wk.2.val = 7 := by simp only [dInf,absDiff] at distant; omega
  exact mateWithin_mono (corner_knight_rescue hq ht (by omega) qx qy wx wy) (by decide)

end EndgameChess.Rules.KQK
