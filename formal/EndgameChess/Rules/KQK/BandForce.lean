import EndgameChess.Rules.KQK.BandRaise

/-! The complete strategy from a prepared separating rank, by a geometric
potential. This is not yet the universal entry theorem for all KQK boards. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem prepared_not_diagonal {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (hc : inCheck q σ.opp = false)
    (hp : Prepared sk qs wk) :
    wk.1.val+qs.2.val ≠ qs.1.val+wk.2.val := by
  intro diagonal
  obtain ⟨below,above,right⟩ := hp.wall
  have see : QueenSees qs wk sk wk := by
    apply sees_split.mpr
    right
    refine ⟨?_,?_,?_⟩
    · simp only [KBK.onDiag,ne_iff_coords,absDiff]; omega
    · simp only [KBK.between,KBK.onDiag,dInf,absDiff,ne_iff_coords]; omega
    · simp [KBK.between,KBK.onDiag]
  have check := (weak_check hq).mpr (Or.inr see)
  rw [hc] at check
  cases check

/-- General prepared-wall forcing. Each defended file step decreases the
potential by two, each rank rise by four, and rank-five/corner finishes
cost at most thirty-three. No position table is used. -/
theorem prepared_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prepared sk qs wk) (hc : inCheck q σ.opp = false) :
    MateWithin σ (bandPotential sk qs+33) q := by
  generalize hpot : bandPotential sk qs = p
  induction p using Nat.strongRecOn generalizing q sk qs wk with
  | ind p ih =>
    by_cases corner : qs.2.val = 5 ∧ wk.1.val = 7 ∧ wk.2.val = 7
    · have rank := hp.kingRank
      have qx : qs.1.val ≠ 5 := by
        have different := prepared_not_diagonal hq hc hp
        omega
      exact mateWithin_mono (rank_five_corner_bound hq ht (by omega) corner.1 qx
        corner.2.1 corner.2.2) (by omega)
    by_cases gap : sk.1.val+2 ≤ wk.1.val
    · obtain ⟨c,su,hl,hm,hct,hne,all,decrease⟩ := prepared_king_step hq ht hp hc gap
      have result : MateWithin σ (p-2+33+2) q := by
        apply mateWithin_pair ht hl hct hne
        intro r hr
        obtain ⟨t,hmt,hrt,next,notCheck⟩ := all r hr
        have smaller : bandPotential su qs < p := by omega
        have win := ih (bandPotential su qs) smaller hmt hrt next notCheck rfl
        exact mateWithin_mono win (by omega)
      exact mateWithin_mono result (by omega)
    have close : wk.1.val ≤ sk.1.val+1 := by omega
    by_cases gap : qs.1.val+2 ≤ wk.1.val
    · have notCorner : qs.2.val < 5 ∨ wk.2.val < 7 ∨ wk.1.val < 7 := by
        have top := hp.top
        have bx := wk.1.isLt
        have by' := wk.2.isLt
        omega
      obtain ⟨c,nq,hl,hm,hct,hne,all,decrease⟩ := prepared_queen_step hq ht hp close gap notCorner
      have result : MateWithin σ (p-2+33+2) q := by
        apply mateWithin_pair ht hl hct hne
        intro r hr
        obtain ⟨t,hmt,hrt,next,notCheck⟩ := all r hr
        have smaller : bandPotential sk nq < p := by omega
        have win := ih (bandPotential sk nq) smaller hmt hrt next notCheck rfl
        exact mateWithin_mono win (by omega)
      exact mateWithin_mono result (by omega)
    have one : qs.1.val+1 = wk.1.val := by have right := hp.wall.2.2; omega
    have far : qs.2.val+2 ≤ wk.2.val := by
      have distant := queen_distant_of_not_check hq hc
      have above := hp.wall.2.1
      simp only [dInf,absDiff] at distant
      omega
    by_cases five : qs.2.val = 5
    · have wy : wk.2.val = 7 := by have bound := wk.2.isLt; omega
      have low : sk.2.val ≤ 4 := by have rank := hp.kingRank; omega
      exact mateWithin_mono (rank_five_knight_bound hq ht low five one wy) (by omega)
    · have low : qs.2.val ≤ 4 := by have top := hp.top; omega
      rw [← hpot]
      apply prepared_raise_bound hq ht hp close one far low
      intro r su nq t hmt hrt next notCheck smaller
      exact ih (bandPotential su nq) (by omega) hmt hrt next notCheck rfl

theorem prepared_seventy_seven {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prepared sk qs wk) (hc : inCheck q σ.opp = false) : MateWithin σ 77 q := by
  have positive : 1 ≤ qs.2.val := by have rank := hp.kingRank; omega
  have bound : bandPotential sk qs ≤ 44 := by simp only [bandPotential]; omega
  exact mateWithin_mono (prepared_bound hq ht hp hc) (by omega)

end EndgameChess.Rules.KQK
