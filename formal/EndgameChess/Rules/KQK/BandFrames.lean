import EndgameChess.Rules.KQK.BandEntry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- Transport absence of a weak-king check to a canonical queen frame. -/
theorem framed_weak_not_check (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (hc : inCheck q σ.opp = false) :
    inCheck (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn) σ.opp = false := by
  have hm : IsKQK (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn)
      σ (g.f sk) (g.f qs) (g.f wk) :=
    ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  cases he : inCheck (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn) σ.opp with
  | false => rfl
  | true =>
    have cases := (weak_check hm).mp he
    have check : inCheck q σ.opp = true := by
      apply (weak_check hq).mpr
      rcases cases with near | ray
      · left; simpa only [g.dInf_eq] using near
      · exact Or.inr ((g.sees_iff qs wk sk wk).mp ray)
    rw [hc] at check
    cases check

/-- A separating rank works on either side of the queen file. -/
theorem separating_rank_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (below : sk.2.val < qs.2.val) (above : qs.2.val < wk.2.val)
    (hc : inCheck q σ.opp = false) : MateWithin σ 91 q := by
  have different : qs.1.val ≠ wk.1.val := by
    intro equal
    have see : QueenSees qs wk sk wk := by
      apply rook_sees_queen
      refine ⟨⟨ne_iff_coords.mp hq.2.2.1,Or.inl equal⟩,?_,not_onSeg_end _ _⟩
      simp only [OnSeg]; omega
    have check := (weak_check hq).mpr (Or.inr see)
    rw [hc] at check
    cases check
  by_cases right : qs.1.val < wk.1.val
  · exact wall_ninety_one hq ht ⟨below,above,right⟩ hc
  · have hm : IsKQK (pos σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) q.turn)
        σ (reflectX.f sk) (reflectX.f qs) (reflectX.f wk) :=
      ⟨reflectX.toBoardSym.ne_iff.mpr hq.1,reflectX.toBoardSym.ne_iff.mpr hq.2.1,
        reflectX.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
    apply unframe_bound reflectX hq
    apply wall_ninety_one hm ht
    · dsimp [Wall,reflectX,symX]; omega
    · exact framed_weak_not_check reflectX hq hc

theorem wall_weak_ninety_two {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (wall : Wall sk qs wk) (band : OpenBand qs) (safe : SafeQueen sk qs wk) :
    MateWithin σ 92 q := by
  apply mateWithin_defend ht (wall_reply_exists hq ht wall band)
  intro r hr
  obtain ⟨t,hm,hrt,wallt,_,_,hc⟩ := wall_reply hq ht wall safe hr
  exact wall_ninety_one hm hrt wallt hc

end EndgameChess.Rules.KQK
