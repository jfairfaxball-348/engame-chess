import EndgameChess.Rules.KRKFiveGeometry

namespace EndgameChess.Rules.KRKSixGeometry
open EndgameChess.KK KRKFiveGeometry
set_option maxHeartbeats 500000

/-- A finite coordinate test built from the seventeen-point five-ply
catalogue, not a recursive future-outcome predicate. A smaller destination
catalogue for the next strong clock band is still required. -/
def Clear (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ (∃ t, KRKCornerWeakBand.Guard sk rs wk t) ∧
    ∀ t, KRKCornerWeakBand.Guard sk rs wk t → KRKFiveGeometry.Clear sk rs t

theorem kernel_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (notMate : ¬MatedK q) :
    MateWithin σ 6 q ↔ Clear sk rs wk := by
  constructor
  · intro win
    have safe := krk_force_weak_safe material turn ⟨6,win⟩
    have data : (∃ r,Legal q r) ∧ ∀ r,Legal q r → MateWithin σ 5 r := by
      rcases win with goal | ⟨_,chosen | defended⟩
      · exact False.elim (notMate goal.2)
      · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
      · exact defended.2
    obtain ⟨r,edge⟩ := data.1
    obtain ⟨t,_,step⟩ := krk_safe_reply material turn safe edge
    refine ⟨safe,⟨t,KRKCornerWeakBand.step_guard step⟩,?_⟩
    intro t guard
    have legal := KRKCornerWeakBand.guard_legal material turn guard
    have next := KRKOppositionHistory.weak_material_after material turn safe legal
    have nextTurn : (play q ⟨wk,t,none⟩).turn = σ := by rw [play_turn,turn,opp_opp]
    obtain ⟨far,notCheck⟩ := krk_strong_arrival_geometry ⟨_,legal,rfl⟩ next nextTurn
    exact (kernel_five_iff next nextTurn far notCheck).mp (data.2 _ ⟨_,legal,rfl⟩)
  · rintro ⟨safe,⟨t,guard⟩,all⟩
    have legal := KRKCornerWeakBand.guard_legal material turn guard
    apply mateWithin_defend turn ⟨_,⟨_,legal,rfl⟩⟩
    intro r edge
    obtain ⟨t,next,step⟩ := krk_safe_reply material turn safe edge
    obtain ⟨far,notCheck⟩ := krk_strong_arrival_geometry edge next.1 next.2
    exact (kernel_five_iff next.1 next.2 far notCheck).mpr (all t (KRKCornerWeakBand.step_guard step))

theorem strong_six_five {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (win : MateWithin σ 6 q) : MateWithin σ 5 q := by
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
    exact mateWithin_choose turn ⟨m,legal,rfl⟩ (KRKFourPlyEscape.weak_five_to_four next nextTurn child)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem weak_seven_six {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (win : MateWithin σ 7 q) : MateWithin σ 6 q := by
  have safe := krk_force_weak_safe material turn ⟨7,win⟩
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · apply mateWithin_defend turn defended.2.1
    intro r edge
    obtain ⟨t,next,_⟩ := krk_safe_reply material turn safe edge
    exact strong_six_five next.1 next.2 (defended.2.2 r edge)

end EndgameChess.Rules.KRKSixGeometry
