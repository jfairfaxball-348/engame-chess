import EndgameChess.Rules.KQK.BandProgress

/-! Raising a prepared separating rank. The queen is prepared exactly one
file behind the weak king before the strong king crosses its rank. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

private theorem king_cross {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prepared sk qs wk) (close : wk.1.val ≤ sk.1.val+1)
    (gap : qs.1.val+1 = wk.1.val) (far : qs.2.val+2 ≤ wk.2.val)
    (low : qs.2.val ≤ 4) :
    ∃ c, Legal q c ∧ IsKQK c σ (wk.1,qs.2) qs wk ∧ c.turn = σ.opp ∧
      (∃ r, Legal c r) ∧
      (∀ r, Legal c r → ∃ t, IsKQK r σ (wk.1,qs.2) qs t ∧ r.turn = σ ∧
        wk.1.val ≤ t.1.val ∧ qs.2.val+2 ≤ t.2.val ∧ inCheck r σ.opp = false) := by
  let su : Square := (wk.1,qs.2)
  have rank := hp.kingRank
  have kingLeft := hp.kingLeft
  obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; omega)
    (by simp only [dInf,absDiff,su]; omega)
  have safe : SafeQueen su qs wk := Or.inr (by simp only [dInf,absDiff,su]; omega)
  have hne : ∃ r, Legal c r := by
    let y : Fin 8 := ⟨if wk.2.val = 7 then 6 else wk.2.val+1,by
      have bound := wk.2.isLt; split <;> omega⟩
    have yProps : absDiff wk.2.val y.val = 1 ∧ qs.2.val+2 ≤ y.val := by
      have bound := wk.2.isLt
      dsimp [y]; split <;> simp only [absDiff] <;> omega
    let t : Square := (wk.1,y)
    obtain ⟨r,hr,_,_⟩ := weak_move (t := t) hm hct
      (by simp only [dInf,absDiff,t] at yProps ⊢; omega)
      (by simp only [ne_iff_coords,t]; omega)
      (by simp only [dInf,absDiff,su,t] at yProps ⊢; omega)
      (by apply not_sees_of_not_line <;> simp only [absDiff,t] <;> omega)
    exact ⟨r,hr⟩
  refine ⟨c,hl,hm,hct,hne,?_⟩
  intro r hr
  obtain ⟨t,hmt,hrt,hd,hfar,hn⟩ := safe_reply hm hct safe hr
  have above : qs.2.val+2 ≤ t.2.val := by
    simp only [dInf,absDiff,su] at hd hfar
    omega
  have right : wk.1.val ≤ t.1.val := by
    by_cases enough : wk.1.val ≤ t.1.val
    · exact enough
    · have equal : t.1.val = qs.1.val := by simp only [dInf,absDiff] at hd; omega
      apply False.elim
      apply hn
      apply rook_sees_queen
      refine ⟨⟨by omega,Or.inl equal.symm⟩,?_,not_onSeg_end _ _⟩
      simp only [OnSeg,su]; omega
  have hc := legal_mover_safe hr
  rw [hct] at hc
  exact ⟨t,hmt,hrt,right,above,hc⟩

/-- A prepared rank can be raised at a cost of four plies. The exceptional
rank-four corner is finished directly in at most thirty-three plies.
The continuation is required only at strictly smaller potential. -/
theorem prepared_raise_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prepared sk qs wk) (close : wk.1.val ≤ sk.1.val+1)
    (gap : qs.1.val+1 = wk.1.val) (far : qs.2.val+2 ≤ wk.2.val)
    (low : qs.2.val ≤ 4)
    (rec : ∀ {r : Position} {su nq t : Square}, IsKQK r σ su nq t → r.turn = σ →
      Prepared su nq t → inCheck r σ.opp = false →
      bandPotential su nq < bandPotential sk qs →
      MateWithin σ (bandPotential su nq+33) r) :
    MateWithin σ (bandPotential sk qs+33) q := by
  obtain ⟨c,hl,hm,hct,hne,all⟩ := king_cross hq ht hp close gap far low
  by_cases corner : qs.2.val = 4 ∧ wk.1.val = 7
  · have result : MateWithin σ 33 q := by
      apply mateWithin_pair ht hl hct hne
      intro r hr
      obtain ⟨t,hmt,hrt,right,above,_⟩ := all r hr
      have wx : t.1.val = 7 := by have bound := t.1.isLt; omega
      let nq : Square := (5,5)
      obtain ⟨u,hu,hum,hut⟩ := queen_move (t := nq) hmt hrt
        (near_sees (by simp only [dInf,absDiff,nq]; omega))
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [dInf,absDiff]; omega)
      exact mateWithin_choose hrt hu (knight_box_weak_bound hum hut
        (by omega) ⟨rfl,rfl,by omega,by omega⟩
        (Or.inl (by simp only [dInf,absDiff,nq]; omega)))
    exact mateWithin_mono result (by omega)
  have result : MateWithin σ (bandPotential sk qs-4+33+4) q := by
    change MateWithin σ (bandPotential sk qs-4+33+2+2) q
    apply mateWithin_pair ht hl hct hne
    intro r hr
    obtain ⟨t,hmt,hrt,right,above,_⟩ := all r hr
    let nq : Square := (qs.1,⟨qs.2.val+1,by omega⟩)
    have newY : nq.2.val = qs.2.val+1 := rfl
    obtain ⟨u,hu,hum,hut⟩ := queen_move (t := nq) hmt hrt
      (near_sees (by simp only [dInf,absDiff,nq]; omega))
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [dInf,absDiff]; omega)
    have next : Prepared (wk.1,qs.2) nq t :=
      ⟨⟨by change qs.2.val < nq.2.val; omega,by omega,by dsimp [nq]; omega⟩,
        by omega,rfl,by dsimp [nq]; omega,right⟩
    have band : OpenBand nq := by
      by_cases lower : qs.2.val ≤ 3
      · exact Or.inl (by omega)
      · have qy : qs.2.val = 4 := by omega
        have wx : wk.1.val ≤ 6 := by have bound := wk.1.isLt; omega
        exact Or.inr ⟨by omega,by dsimp [nq]; omega⟩
    have safe : SafeQueen (wk.1,qs.2) nq t :=
      Or.inr (by simp only [dInf,absDiff,nq]; omega)
    apply mateWithin_pair hrt hu hut (wall_reply_exists hum hut next.wall band)
    intro v hv
    obtain ⟨z,hmz,hzt,wall,_,_,hc⟩ := wall_reply hum hut next.wall safe hv
    have prepared : Prepared (wk.1,qs.2) nq z :=
      ⟨wall,next.top,next.kingRank,next.queenLeft,by
        change wk.1.val ≤ z.1.val
        have := wall.2.2
        dsimp [nq] at this
        omega⟩
    have decrease : bandPotential (wk.1,qs.2) nq+4 ≤ bandPotential sk qs := by
      have kingLeft := hp.kingLeft
      have bx := wk.1.isLt
      simp only [bandPotential,nq]; omega
    have win := rec hmz hzt prepared hc (by omega)
    exact mateWithin_mono win (by omega)
  have positive : 4 ≤ bandPotential sk qs := by simp only [bandPotential]; omega
  exact mateWithin_mono result (by omega)

end EndgameChess.Rules.KQK
