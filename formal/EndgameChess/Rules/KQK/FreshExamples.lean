import EndgameChess.Rules.KQK.FreshOutcome
import EndgameChess.Rules.KQK.Examples

/-! Local non-vacuity controls for the class theorem, not a position table. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

theorem fresh_white_win_example :
    FreshGame.ActualWin .white (FreshGame.fresh (pos .white (0,0) (0,1) (7,7) .white)) := by
  apply (fresh_wdl50 (σ := .white) (sk := (0,0)) (qs := (0,1)) (wk := (7,7))
    ⟨by decide,by decide,by decide,rfl⟩ ⟨rfl,rfl,by decide,by decide⟩).1.mpr
  exact Or.inl rfl

theorem fresh_black_queen_weak_turn_example :
    FreshGame.ActualWin .black (FreshGame.fresh (pos .black (0,0) (0,1) (7,7) .white)) := by
  let q := pos .black (0,0) (0,1) (7,7) .white
  have hm : IsKQK q .black (0,0) (0,1) (7,7) := ⟨by decide,by decide,by decide,rfl⟩
  have legal : FreshLegal q (0,0) (7,7) := ⟨rfl,rfl,by decide,by decide⟩
  obtain ⟨r,hr,_,_⟩ := weak_move (t := (7,6)) hm rfl (by decide) (by decide)
    (by decide) (by apply not_sees_of_not_line <;> decide)
  exact (fresh_wdl50 hm legal).1.mpr (Or.inr (Or.inr ⟨Or.inl (by decide),r,hr⟩))

theorem fresh_stalemate_draw_example :
    FreshGame.Hold .white (FreshGame.fresh stalemateExample) ∧
      FreshGame.Hold .black (FreshGame.fresh stalemateExample) := by
  have hm : IsKQK stalemateExample .white (2,5) (1,5) (0,7) :=
    ⟨by decide,by decide,by decide,rfl⟩
  have legal : FreshLegal stalemateExample (2,5) (0,7) := ⟨rfl,rfl,by decide,by decide⟩
  apply (fresh_wdl50 hm legal).2.2.mpr
  intro criterion
  exact stalemate_example_no_force ((board_outcome_iff hm (fun ht => by cases ht)).mpr criterion)

/-- Drawn but not dead: Black may capture Qd4, or cooperate with Ke6,
after which the universal strong-turn theorem supplies possible mate. -/
theorem fresh_live_draw_example :
    let q := pos .white (0,0) (3,3) (3,4) .black
    FreshGame.Hold .white (FreshGame.fresh q) ∧
      FreshGame.Hold .black (FreshGame.fresh q) ∧ ¬ DeadK q := by
  let q := pos .white (0,0) (3,3) (3,4) .black
  have hm : IsKQK q .white (0,0) (3,3) (3,4) := ⟨by decide,by decide,by decide,rfl⟩
  have legal : FreshLegal q (0,0) (3,4) := ⟨rfl,rfl,by decide,by decide⟩
  obtain ⟨u,hu,_,_,_⟩ := LoneKing.unprotected_capture (by decide : PieceType.queen ≠ .king)
    hm rfl (by decide) (by decide)
  have noCriterion : ¬ WinningCriterion .white q (0,0) (3,3) (3,4) := by
    rintro (wrong | mate | ⟨safe,_⟩)
    · exact (by decide : Colour.black ≠ .white) wrong
    · exact mate.2 ⟨u,hu⟩
    · exact (by unfold SafeQueen LoneKing.Safe; decide : ¬ SafeQueen (0,0) (3,3) (3,4)) safe
  have holding := (fresh_wdl50 hm legal).2.2.mpr noCriterion
  obtain ⟨r,hr,hmr,hrt⟩ := weak_move (t := (4,5)) hm rfl (by decide) (by decide)
    (by decide) (by apply not_sees_of_not_line <;> decide)
  have live := forceMate_not_dead (show ForceMate .white r from ⟨97,strong_arrival_bound hmr hrt ⟨q,hr⟩⟩)
  refine ⟨holding.1,holding.2,?_⟩
  intro dead
  apply live
  rintro ⟨t,reach,mate⟩
  exact dead ⟨t,reachK_cons hr reach,mate⟩

end EndgameChess.Rules.KQK
