import EndgameChess.Rules.KQK.Setup

/-! A checking staircase aligns queens farther than a knight offset away.
The rank changes are defended universally; the proof uses a linear potential. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def Staircase (sk qs wk : Square) : Prop :=
  sk.1.val+sk.2.val ≤ 4 ∧ qs.1.val+2 ≤ wk.1.val ∧
    absDiff qs.2.val wk.2.val = 1 ∧ 6 ≤ qs.1.val+wk.2.val

def staircasePotential (qs wk : Square) : Nat := 7+wk.1.val-2*qs.1.val

private theorem staircase_step {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hs : Staircase sk qs wk) (gap : qs.1.val+3 ≤ wk.1.val) :
    ∃ c nq, Legal q c ∧ IsKQK c σ sk nq wk ∧ c.turn = σ.opp ∧
      (∃ r, Legal c r) ∧
      ∀ r, Legal c r → ∃ t, IsKQK r σ sk nq t ∧ r.turn = σ ∧
        Staircase sk nq t ∧ staircasePotential nq t < staircasePotential qs wk := by
  obtain ⟨low,_,nearRank,progress⟩ := hs
  have wxBound := wk.1.isLt
  have wyBound := wk.2.isLt
  have high : 9 ≤ wk.1.val+wk.2.val := by omega
  let nq : Square := (⟨qs.1.val+1,by omega⟩,wk.2)
  have nqx : nq.1.val = qs.1.val+1 := rfl
  have nqy : nq.2.val = wk.2.val := rfl
  have qsum : 7 ≤ nq.1.val+nq.2.val := by dsimp [nq]; omega
  have qstep : dInf qs nq = 1 := by simp only [dInf,absDiff,nq] at nearRank ⊢; omega
  obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht (near_sees qstep)
    (by simp only [ne_iff_coords]; omega)
    (by simp only [ne_iff_coords,nq]; omega) (sum_far low (by omega))
  let y : Fin 8 := ⟨if h : wk.2.val < 7 then wk.2.val+1 else wk.2.val-1,
    by split <;> omega⟩
  let t : Square := (wk.1,y)
  have y2 : 2 ≤ wk.2.val := by omega
  have step : dInf wk t = 1 := by
    dsimp [t,y]; split <;> simp only [dInf,absDiff] <;> omega
  have highT : 8 ≤ t.1.val+t.2.val := by dsimp [t,y]; split <;> omega
  have ne : t ≠ nq := by simp only [ne_iff_coords,t,nq]; omega
  have unseen : ¬ QueenSees nq t sk t := by
    dsimp [t,y]; split <;> apply not_sees_of_not_line <;>
      simp only [absDiff,nq] <;> omega
  obtain ⟨r,hr,_,_⟩ := weak_move hm hc step ne (sum_far low highT) unseen
  refine ⟨c,nq,hl,hm,hc,⟨r,hr⟩,?_⟩
  intro r hr
  have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
  obtain ⟨t,hmt,hrt,hd,_,hn⟩ := safe_reply hm hc safe hr
  have tx : nq.1.val+1 ≤ t.1.val := by simp only [dInf,absDiff,nq] at hd ⊢; omega
  have differentRank : t.2.val ≠ wk.2.val := by
    intro equal
    apply hn
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inr (by dsimp [nq]; omega)⟩,?_,not_onSeg_end _ _⟩
    simp only [OnSeg]; dsimp [nq] at qsum ⊢; omega
  have nextRank : absDiff nq.2.val t.2.val = 1 := by
    simp only [dInf,absDiff,nq] at hd ⊢; omega
  have nextGap : nq.1.val+2 ≤ t.1.val := by
    by_cases enough : nq.1.val+2 ≤ t.1.val
    · exact enough
    · have near : dInf nq t = 1 := by simp only [dInf,absDiff] at nextRank ⊢; omega
      exact False.elim (hn (near_sees near))
  have nextProgress : 6 ≤ nq.1.val+t.2.val := by
    simp only [dInf,absDiff,nq] at hd ⊢; omega
  have decrease : staircasePotential nq t < staircasePotential qs wk := by
    simp only [dInf,absDiff] at hd
    simp only [staircasePotential,nq]
    omega
  exact ⟨t,hmt,hrt,⟨low,nextGap,nextRank,nextProgress⟩,decrease⟩

/-- A distant queen can staircase toward the two-file finish while the
strong king stays outside. The potential decreases on every defended pair. -/
theorem staircase_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hs : Staircase sk qs wk) :
    MateWithin σ (2*staircasePotential qs wk+53) q := by
  generalize hp : staircasePotential qs wk = p
  induction p using Nat.strongRecOn generalizing q qs wk with
  | ind p ih =>
    by_cases finish : qs.1.val+2 = wk.1.val
    · have low := hs.1
      have progress := hs.2.2.2
      have high : 8 ≤ wk.1.val+wk.2.val := by omega
      exact mateWithin_mono (two_file_entry_bound hq ht low high finish hs.2.2.1) (by omega)
    · have gap : qs.1.val+3 ≤ wk.1.val := by have oldGap := hs.2.1; omega
      obtain ⟨c,nq,hl,hm,hc,hne,all⟩ := staircase_step hq ht hs gap
      change MateWithin σ (2*p+51+2) q
      apply mateWithin_pair ht hl hc hne
      intro r hr
      obtain ⟨t,hmt,hrt,hst,decrease⟩ := all r hr
      have smaller : staircasePotential nq t < p := by omega
      have result := ih (staircasePotential nq t) smaller hmt hrt hst rfl
      exact mateWithin_mono result (by omega)

theorem staircase_eighty_one {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hs : Staircase sk qs wk) : MateWithin σ 81 q := by
  have p : staircasePotential qs wk ≤ 14 := by
    have bound := wk.1.isLt
    simp only [staircasePotential]; omega
  exact mateWithin_mono (staircase_bound hq ht hs) (by omega)

theorem framed_staircase_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hs : Staircase (g.f sk) (g.f qs) (g.f wk)) : MateWithin σ 81 q := by
  apply unframe_bound g hq
  apply staircase_eighty_one
  · exact ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  · exact ht
  · exact hs

end EndgameChess.Rules.KQK
